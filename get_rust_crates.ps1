<#
.SYNOPSIS
    Fetch a crates.io crate and ALL its recursive dependencies without cargo.

.DESCRIPTION
    Resolves dependencies with a cargo-style resolver and downloads every
    resulting .crate file (verifying SHA-256 against the index). It does NOT
    vendor: no cargo-vendor directory layout, no .cargo-checksum.json files and
    no config snippet. Output:

        <OutDir>\<name>-<version>.crate     one archive per resolved package
        <OutDir>\crates.csv                 name, version, sha256 of everything fetched
        <OutDir>\src\<name>-<version>\      only with -Extract

    Resolver behaviour (modelled on cargo's):
      * Depth-first search, highest version first, with backtracking and
        conflict-driven backjumping when a choice leads to a dead end.
      * At most one version per semver-compatible range (1.x, 0.2.x, 0.0.3).
      * `links` conflicts are honoured (two crates can't claim the same native lib).
      * Features are resolved together with versions (feature unification,
        `dep:`, `pkg/feat`, `pkg?/feat`, implicit optional-dep features).
      * Most-constrained dependency (fewest candidates) is processed first.
      * Root crate behaves like a workspace member: all features on, dev-deps
        included. All targets (cfg(windows), cfg(unix), ...) and build-deps are
        included, as in Cargo.lock.
      * Yanked versions are never selected.

    Not replicated: MSRV-aware resolution, git/path/alternate-registry deps,
    and cargo's exact tie-breaking, so results can differ from cargo in corner cases.

.EXAMPLE
    .\Get-RustCrate-NoVendor.ps1 -Name serde_json

.EXAMPLE
    .\Get-RustCrate-NoVendor.ps1 -Name tokio -Version 1.38.0 -OutDir C:\work\crates -Extract -Verbose
#>
[CmdletBinding()]
param(
    [Parameter(Mandatory)][string]$Name,
    [string]$Version,                        # exact root version (default: latest stable, non-yanked)
    [string]$OutDir = ".\crates",
    [switch]$Extract,                        # also untar each crate into <OutDir>\src
    [switch]$NoAllFeatures,                  # don't force all features on the root crate
    [string[]]$Features = @(),
    [switch]$NoDefaultFeatures,
    [switch]$NoDevDeps,                      # skip root's dev-dependencies
    [switch]$NoBuildDeps,
    [switch]$NoTargetSpecific,
    [switch]$IncludeOptional                 # extra: include optional deps of EVERY crate
)

$ErrorActionPreference = 'Stop'
[Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12
$ProgressPreference = 'SilentlyContinue'
$UserAgent = 'Get-RustCrate.ps1 (powershell script)'

# =============================================================== semver ====

function ConvertTo-SemVer([string]$s) {
    $rx = '^\s*v?(\d+|\*|x|X)(?:\.(\d+|\*|x|X))?(?:\.(\d+|\*|x|X))?(?:-([0-9A-Za-z.-]+))?(?:\+[0-9A-Za-z.-]+)?\s*$'
    $m = [regex]::Match($s, $rx)
    if (-not $m.Success) { throw "Cannot parse version '$s'" }
    $n = 0
    $nums = @(0, 0, 0)
    foreach ($i in 0..2) {
        $g = $m.Groups[$i + 1]
        if ($g.Success -and $g.Value -match '^\d+$') { $nums[$i] = [long]$g.Value; $n++ } else { break }
    }
    @{ Major = $nums[0]; Minor = $nums[1]; Patch = $nums[2]; Pre = $m.Groups[4].Value; N = $n }
}

function Compare-SemVer($a, $b) {
    foreach ($f in 'Major', 'Minor', 'Patch') {
        if ($a[$f] -ne $b[$f]) { return [Math]::Sign([long]$a[$f] - [long]$b[$f]) }
    }
    if ($a.Pre -eq $b.Pre) { return 0 }
    if (-not $a.Pre) { return 1 }
    if (-not $b.Pre) { return -1 }
    $x = $a.Pre.Split('.'); $y = $b.Pre.Split('.')
    for ($i = 0; $i -lt [Math]::Min($x.Count, $y.Count); $i++) {
        $xn = $x[$i] -match '^\d+$'; $yn = $y[$i] -match '^\d+$'
        if ($xn -and $yn) {
            $d = [long]$x[$i] - [long]$y[$i]
            if ($d -ne 0) { return [Math]::Sign($d) }
        }
        elseif ($xn) { return -1 }
        elseif ($yn) { return 1 }
        else {
            $c = [string]::CompareOrdinal($x[$i], $y[$i])
            if ($c -ne 0) { return [Math]::Sign($c) }
        }
    }
    return [Math]::Sign($x.Count - $y.Count)
}

# Semver-compatibility range, i.e. the unit cargo allows exactly one version of
function Get-CompatKey($v) {
    if ($v.Major -gt 0) { return "$($v.Major)" }
    if ($v.Minor -gt 0) { return "0.$($v.Minor)" }
    return "0.0.$($v.Patch)"
}

function New-Bound($maj, $min, $pat) { @{ Major = [long]$maj; Minor = [long]$min; Patch = [long]$pat; Pre = '' } }

# Parses "^1.2, <1.5" etc. Bounds are precomputed once per requirement string.
function ConvertTo-Req([string]$req) {
    $comps = @()
    foreach ($part in $req.Split(',')) {
        $p = $part.Trim()
        if ($p -eq '' -or $p -eq '*') { $comps += @{ Op = '*'; V = $null; N = 0; Low = $null; Hi = $null }; continue }
        $m = [regex]::Match($p, '^(\^|~|=|>=|<=|>|<)?\s*(.+)$')
        $op = if ($m.Groups[1].Success) { $m.Groups[1].Value } else { '^' }
        $v = ConvertTo-SemVer $m.Groups[2].Value
        $c = @{ Op = $op; V = $v; N = $v.N; Hi = $null
                Low = @{ Major = $v.Major; Minor = $v.Minor; Patch = $v.Patch; Pre = $v.Pre } }
        if ($v.N -eq 0) { $c.Op = '*' }
        else {
            $M = $v.Major; $mi = $v.Minor; $pa = $v.Patch; $n = $v.N
            if ($op -eq '^') {
                if ($n -eq 1 -or $M -gt 0) { $c.Hi = New-Bound ($M + 1) 0 0 }
                elseif ($n -eq 2 -or $mi -gt 0) { $c.Hi = New-Bound 0 ($mi + 1) 0 }
                else { $c.Hi = New-Bound 0 0 ($pa + 1) }
            }
            elseif ($op -eq '~') {
                if ($n -eq 1) { $c.Hi = New-Bound ($M + 1) 0 0 } else { $c.Hi = New-Bound $M ($mi + 1) 0 }
            }
            else {
                switch ($n) {
                    1 { $c.Hi = New-Bound ($M + 1) 0 0 }
                    2 { $c.Hi = New-Bound $M ($mi + 1) 0 }
                    3 { $c.Hi = New-Bound $M $mi ($pa + 1) }
                }
            }
        }
        $comps += $c
    }
    , $comps
}

$script:ReqCache = @{}
function Get-Req([string]$s) {
    if (-not $script:ReqCache.ContainsKey($s)) { $script:ReqCache[$s] = ConvertTo-Req $s }
    return , $script:ReqCache[$s]
}

function Test-Comparator($v, $c) {
    switch ($c.Op) {
        '*'  { return $true }
        '='  {
            if ($c.N -eq 3) { return (Compare-SemVer $v $c.Low) -eq 0 }
            return ((Compare-SemVer $v $c.Low) -ge 0 -and (Compare-SemVer $v $c.Hi) -lt 0)
        }
        '>'  {
            if ($c.N -eq 3) { return (Compare-SemVer $v $c.Low) -gt 0 }
            return (Compare-SemVer $v $c.Hi) -ge 0
        }
        '>=' { return (Compare-SemVer $v $c.Low) -ge 0 }
        '<'  { return (Compare-SemVer $v $c.Low) -lt 0 }
        '<=' {
            if ($c.N -eq 3) { return (Compare-SemVer $v $c.Low) -le 0 }
            return (Compare-SemVer $v $c.Hi) -lt 0
        }
        { $_ -eq '^' -or $_ -eq '~' } {
            return ((Compare-SemVer $v $c.Low) -ge 0 -and (Compare-SemVer $v $c.Hi) -lt 0)
        }
    }
    return $false
}

function Test-Req($v, $comps) {
    foreach ($c in $comps) { if (-not (Test-Comparator $v $c)) { return $false } }
    if ($v.Pre) {
        # pre-releases match only if a comparator names a pre-release of the same x.y.z
        foreach ($c in $comps) {
            if ($c.V -and $c.V.Pre -and $c.V.Major -eq $v.Major -and $c.V.Minor -eq $v.Minor -and $c.V.Patch -eq $v.Patch) { return $true }
        }
        return $false
    }
    return $true
}

# ========================================================== crates index ====

$script:IndexCache = @{}
$script:CandCache  = @{}

function Get-IndexPath([string]$n) {
    $n = $n.ToLower()
    switch ($n.Length) {
        1       { return "1/$n" }
        2       { return "2/$n" }
        3       { return "3/$($n.Substring(0,1))/$n" }
        default { return "$($n.Substring(0,2))/$($n.Substring(2,2))/$n" }
    }
}

# All versions of a crate, sorted newest first
function Get-CrateVersions([string]$n) {
    $key = $n.ToLower()
    if (-not $script:IndexCache.ContainsKey($key)) {
        $url = "https://index.crates.io/$(Get-IndexPath $n)"
        try {
            $resp = Invoke-WebRequest -Uri $url -UseBasicParsing -Headers @{ 'User-Agent' = $UserAgent }
        }
        catch {
            throw "Crate '$n' not found in index ($url): $($_.Exception.Message)"
        }
        $text = $resp.Content
        if ($text -is [byte[]]) { $text = [Text.Encoding]::UTF8.GetString($text) }
        $list = New-Object 'System.Collections.Generic.List[object]'
        foreach ($line in ($text -split "`n")) {
            if ([string]::IsNullOrWhiteSpace($line)) { continue }
            $e = $line | ConvertFrom-Json
            $v = ConvertTo-SemVer $e.vers
            $list.Add(@{ Entry = $e; V = $v; Group = ("{0}|{1}" -f $e.name.ToLower(), (Get-CompatKey $v)) })
        }
        $cmp = [System.Comparison[object]] { param($x, $y) Compare-SemVer $y.V $x.V }
        $list.Sort($cmp)
        $script:IndexCache[$key] = $list
    }
    return $script:IndexCache[$key]
}

# Non-yanked versions of $name matching $req, newest first (cached; state independent)
function Get-Candidates([string]$name, [string]$req) {
    $ck = "$($name.ToLower())|$req"
    if (-not $script:CandCache.ContainsKey($ck)) {
        $comps = Get-Req $req
        $out = New-Object System.Collections.ArrayList
        foreach ($it in (Get-CrateVersions $name)) {
            if ($it.Entry.yanked) { continue }
            if (Test-Req $it.V $comps) { [void]$out.Add($it) }
        }
        $script:CandCache[$ck] = $out
    }
    return , $script:CandCache[$ck]
}

function Get-FeatureMap($entry) {
    $m = @{}
    foreach ($src in @($entry.features, $entry.features2)) {
        if ($src) { foreach ($p in $src.PSObject.Properties) { $m[$p.Name] = @($p.Value) } }
    }
    $m
}
function Get-ItemFM($item) {
    if (-not $item.ContainsKey('FM')) { $item['FM'] = Get-FeatureMap $item.Entry }
    return $item['FM']
}
function Get-ItemOpt($item) {
    if (-not $item.ContainsKey('Opt')) {
        $o = @{}
        foreach ($d in @($item.Entry.deps)) { if ($d -and $d.optional) { $o[$d.name] = $true } }
        $item['Opt'] = $o
    }
    return $item['Opt']
}

# ===================================================== resolver state ====
# Node records are treated as immutable: they are copied before being changed,
# so a state snapshot is just a shallow clone of the tables below.

$script:Act      = @{}                                       # group key -> node record
$script:Seen     = @{}                                       # edge signatures already queued
$script:Pending  = New-Object System.Collections.ArrayList   # edges, sorted; last = next to process
$script:Links    = @{}                                       # links value -> group key
$script:Stack    = New-Object System.Collections.ArrayList   # backtrack frames
$script:Seq      = 0
$script:Backtracks = 0
$script:Fail     = ''
$script:FeatChanged = $false
$script:WarnedRegistry = $false

function Copy-Set($s) {
    $a = [string[]]@($s)
    return , ([System.Collections.Generic.HashSet[string]]::new($a))
}

function New-NodeRecord($item, [bool]$isRoot) {
    @{
        Key     = $item.Group
        Item    = $item
        IsRoot  = $isRoot
        Feats   = (New-Object 'System.Collections.Generic.HashSet[string]')
        EnDeps  = (New-Object 'System.Collections.Generic.HashSet[string]')
        Child   = @{}      # dep local name -> set of features requested for it
        Contrib = @{}      # group keys that (transitively) caused this node's features
    }
}

function Copy-Node($n) {
    $child = @{}
    foreach ($k in $n.Child.Keys) { $child[$k] = Copy-Set $n.Child[$k] }
    @{
        Key = $n.Key; Item = $n.Item; IsRoot = $n.IsRoot
        Feats = (Copy-Set $n.Feats); EnDeps = (Copy-Set $n.EnDeps)
        Child = $child; Contrib = $n.Contrib.Clone()
    }
}

function Get-Snapshot {
    @{ Act = $script:Act.Clone(); Seen = $script:Seen.Clone(); Pending = $script:Pending.Clone(); Links = $script:Links.Clone() }
}
function Restore-Snapshot($s) {
    $script:Act = $s.Act.Clone()
    $script:Seen = $s.Seen.Clone()
    $script:Pending = $s.Pending.Clone()
    $script:Links = $s.Links.Clone()
}

# ------------------------------------------------------------ features ----

function Enable-Dep($node, [string]$d) {
    if ($node.EnDeps.Add($d)) { $script:FeatChanged = $true }
}

function Enable-Feature($node, [string]$f) {
    if (-not $node.Feats.Add($f)) { return }
    $script:FeatChanged = $true
    $fm = Get-ItemFM $node.Item
    $opt = Get-ItemOpt $node.Item
    if ($fm.ContainsKey($f)) {
        foreach ($item in $fm[$f]) {
            if ($item.StartsWith('dep:')) {
                Enable-Dep $node $item.Substring(4)
            }
            elseif ($item.Contains('/')) {
                $slash = $item.IndexOf('/')
                $d = $item.Substring(0, $slash)
                $cf = $item.Substring($slash + 1)
                $weak = $d.EndsWith('?')
                if ($weak) { $d = $d.TrimEnd('?') }
                if (-not $node.Child.ContainsKey($d)) {
                    $node.Child[$d] = New-Object 'System.Collections.Generic.HashSet[string]'
                }
                if ($node.Child[$d].Add($cf)) { $script:FeatChanged = $true }
                if (-not $weak -and $opt.ContainsKey($d)) { Enable-Dep $node $d }
            }
            else {
                Enable-Feature $node $item
            }
        }
    }
    elseif ($opt.ContainsKey($f)) {
        Enable-Dep $node $f        # implicit feature named after an optional dependency
    }
}

function Add-NodeFeatures($node, $feats, [bool]$useDef) {
    $script:FeatChanged = $false
    if ($useDef) { Enable-Feature $node 'default' }
    foreach ($f in @($feats)) { if ($f) { Enable-Feature $node ([string]$f) } }
    return $script:FeatChanged
}

function Test-FeaturesCovered($node, $feats, [bool]$useDef) {
    if ($useDef -and -not $node.Feats.Contains('default')) { return $false }
    foreach ($f in @($feats)) { if ($f -and -not $node.Feats.Contains([string]$f)) { return $false } }
    return $true
}

# --------------------------------------------------------------- edges ----

function Insert-Edge($edge) {
    $lo = 0; $hi = $script:Pending.Count
    while ($lo -lt $hi) {
        $mid = ($lo + $hi) -shr 1
        if ($script:Pending[$mid].Sort -lt $edge.Sort) { $lo = $mid + 1 } else { $hi = $mid }
    }
    $script:Pending.Insert($lo, $edge)
}

# Queue the dependency edges a node currently activates (idempotent via $script:Seen)
function Add-NodeEdges($node) {
    $e = $node.Item.Entry
    $i = -1
    foreach ($d in @($e.deps)) {
        $i++
        if ($null -eq $d) { continue }
        $kind = if ($d.kind) { $d.kind } else { 'normal' }
        if ($kind -eq 'dev' -and -not ($node.IsRoot -and -not $NoDevDeps)) { continue }
        if ($kind -eq 'build' -and $NoBuildDeps) { continue }
        if ($d.target -and $NoTargetSpecific) { continue }
        if ($d.registry) {
            if (-not $script:WarnedRegistry) { Write-Warning "Skipping dependencies from alternate registries (e.g. $($d.name))."; $script:WarnedRegistry = $true }
            continue
        }
        $local = $d.name
        if ($d.optional -and -not $IncludeOptional -and -not $node.EnDeps.Contains($local)) { continue }

        $real = if ($d.package) { $d.package } else { $d.name }
        $fl = New-Object System.Collections.Generic.List[string]
        foreach ($f in @($d.features)) { if ($f) { $fl.Add([string]$f) } }
        if ($node.Child.ContainsKey($local)) { foreach ($f in $node.Child[$local]) { $fl.Add($f) } }
        $fa = [string[]]@($fl | Select-Object -Unique)
        if ($fa.Count -gt 1) { [Array]::Sort($fa, [StringComparer]::Ordinal) }
        $useDef = if ($null -ne $d.default_features) { [bool]$d.default_features } else { $true }

        $sig = "{0}|{1}|{2}|{3}" -f $node.Key, $i, ($fa -join ','), $useDef
        if ($script:Seen.ContainsKey($sig)) { continue }
        $script:Seen[$sig] = $true

        $cnt = (Get-Candidates $real $d.req).Count
        $script:Seq++
        Insert-Edge @{
            Parent     = $node.Key
            ParentDesc = "$($e.name) $($e.vers)"
            Name       = $real
            Req        = $d.req
            Comps      = (Get-Req $d.req)
            Feats      = $fa
            UseDef     = $useDef
            Sort       = ([double](-$cnt) * 10000000 + $script:Seq)   # fewest candidates last => popped first; ties: newest first
        }
    }
}

# ------------------------------------------------------ candidate choice ----

# Candidates for an edge, honouring "one version per compatible range" and `links`
function Select-Candidates($edge) {
    $cands = Get-Candidates $edge.Name $edge.Req
    $list = New-Object System.Collections.ArrayList
    $conf = @{}
    $groups = @{}      # group -> 0 (decided by an active node) | 1 (free)
    foreach ($it in $cands) {
        $g = $it.Group
        if (-not $groups.ContainsKey($g)) {
            if ($script:Act.ContainsKey($g)) {
                $act = $script:Act[$g]
                if (Test-Req $act.Item.V $edge.Comps) { [void]$list.Add($act.Item) } else { $conf[$g] = $true }
                $groups[$g] = 0
            }
            else { $groups[$g] = 1 }
        }
        if ($groups[$g] -eq 0) { continue }
        $lk = $it.Entry.links
        if ($lk -and $script:Links.ContainsKey($lk) -and $script:Links[$lk] -ne $g) {
            $conf[$script:Links[$lk]] = $true
            continue
        }
        [void]$list.Add($it)
    }
    if ($list.Count -eq 0) {
        if ($cands.Count -eq 0) {
            $script:Fail = "no version of '$($edge.Name)' matches '$($edge.Req)' (required by $($edge.ParentDesc))"
        }
        else {
            $script:Fail = "all candidates for '$($edge.Name) $($edge.Req)' (required by $($edge.ParentDesc)) conflict with already selected packages: $(($conf.Keys | Sort-Object) -join ', ')"
        }
    }
    @{ List = $list; Conf = $conf }
}

function Apply-Candidate($edge, $item) {
    $g = $item.Group
    $parent = $script:Act[$edge.Parent]

    if ($script:Act.ContainsKey($g)) {
        $cur = $script:Act[$g]
        $needFeat = -not (Test-FeaturesCovered $cur $edge.Feats $edge.UseDef)
        $needContrib = -not $cur.Contrib.ContainsKey($edge.Parent)
        if (-not $needContrib) { foreach ($k in $parent.Contrib.Keys) { if (-not $cur.Contrib.ContainsKey($k)) { $needContrib = $true; break } } }
        if (-not ($needFeat -or $needContrib)) { return }
        $node = Copy-Node $cur
        $changed = $false
        if ($needFeat) { $changed = Add-NodeFeatures $node $edge.Feats $edge.UseDef }
        $node.Contrib[$edge.Parent] = $true
        foreach ($k in $parent.Contrib.Keys) { $node.Contrib[$k] = $true }
        $script:Act[$g] = $node
        if ($changed) { Add-NodeEdges $node }
    }
    else {
        $node = New-NodeRecord $item $false
        [void](Add-NodeFeatures $node $edge.Feats $edge.UseDef)
        $node.Contrib[$edge.Parent] = $true
        foreach ($k in $parent.Contrib.Keys) { $node.Contrib[$k] = $true }
        $script:Act[$g] = $node
        if ($item.Entry.links) { $script:Links[$item.Entry.links] = $g }
        Write-Verbose ("  + {0} {1}" -f $item.Entry.name, $item.Entry.vers)
        Add-NodeEdges $node
    }
}

# ------------------------------------------------------------ backtracking ----

function Add-Blame($C, [string]$parentKey, $act) {
    $C[$parentKey] = $true
    if ($act.ContainsKey($parentKey)) { foreach ($k in $act[$parentKey].Contrib.Keys) { $C[$k] = $true } }
}

# $C = set of group keys responsible for the failure. Pops frames until one whose
# alternatives could change the outcome (cargo-style backjumping), then applies the
# next candidate. Returns $false when there is nothing left to try.
function Invoke-Backtrack([hashtable]$C) {
    while ($true) {
        if ($script:Stack.Count -eq 0) { return $false }
        $F = $script:Stack[$script:Stack.Count - 1]
        $script:Stack.RemoveAt($script:Stack.Count - 1)

        # If every conflicting package already existed before this decision, changing
        # this decision cannot help.
        $relevant = $false
        foreach ($k in $C.Keys) { if (-not $F.Snap.Act.ContainsKey($k)) { $relevant = $true; break } }
        if (-not $relevant) { continue }
        foreach ($k in $C.Keys) { $F.Conf[$k] = $true }

        if ($F.Idx -ge $F.List.Count) {
            # every candidate of this decision failed: blame what existed before it
            $newC = @{}
            foreach ($k in $F.Conf.Keys) { if ($F.Snap.Act.ContainsKey($k)) { $newC[$k] = $true } }
            Add-Blame $newC $F.Edge.Parent $F.Snap.Act
            $C = $newC
            continue
        }

        Restore-Snapshot $F.Snap
        $next = $F.List[$F.Idx]
        $F.Idx++
        [void]$script:Stack.Add($F)      # stays until all its candidates are exhausted
        $script:Backtracks++
        Write-Verbose ("  backtrack -> {0} {1}" -f $next.Entry.name, $next.Entry.vers)
        Apply-Candidate $F.Edge $next
        return $true
    }
}

# ============================================================ main: resolve ====

Write-Host "Resolving $Name ..."
$versions = Get-CrateVersions $Name
$rootItem = $null
if ($Version) {
    $want = ConvertTo-SemVer $Version
    foreach ($it in $versions) { if ((Compare-SemVer $it.V $want) -eq 0) { $rootItem = $it } }
    if (-not $rootItem) { throw "Version $Version of '$Name' not found" }
}
else {
    foreach ($it in $versions) {      # sorted newest first
        if ($it.Entry.yanked -or $it.V.Pre) { continue }
        $rootItem = $it; break
    }
    if (-not $rootItem) { throw "No stable, non-yanked version of '$Name' found" }
}

$root = New-NodeRecord $rootItem $true
if (-not $NoAllFeatures) {
    foreach ($k in @((Get-ItemFM $rootItem).Keys)) { Enable-Feature $root $k }
    foreach ($o in @((Get-ItemOpt $rootItem).Keys)) { Enable-Dep $root $o }
}
[void](Add-NodeFeatures $root $Features (-not $NoDefaultFeatures))
$script:Act[$root.Key] = $root
if ($rootItem.Entry.links) { $script:Links[$rootItem.Entry.links] = $root.Key }
Add-NodeEdges $root

while ($script:Pending.Count -gt 0) {
    $edge = $script:Pending[$script:Pending.Count - 1]
    $script:Pending.RemoveAt($script:Pending.Count - 1)

    $sel = Select-Candidates $edge
    if ($sel.List.Count -eq 0) {
        $C = @{}
        foreach ($k in $sel.Conf.Keys) { $C[$k] = $true }
        Add-Blame $C $edge.Parent $script:Act
        Write-Verbose "  conflict: $script:Fail"
        if (-not (Invoke-Backtrack $C)) {
            throw "Failed to resolve dependencies:`n  $script:Fail"
        }
        continue
    }
    if ($sel.List.Count -gt 1) {
        [void]$script:Stack.Add(@{ Snap = (Get-Snapshot); Edge = $edge; List = $sel.List; Idx = 1; Conf = $sel.Conf })
    }
    Apply-Candidate $edge $sel.List[0]
}

$resolved = @()
foreach ($n in $script:Act.Values) { $resolved += @{ Entry = $n.Item.Entry; V = $n.Item.V } }
$resolved = $resolved | Sort-Object { $_.Entry.name }, { $_.Entry.vers }

Write-Host ("Resolved {0} packages ({1} backtracks):" -f $resolved.Count, $script:Backtracks)
foreach ($n in $resolved) { Write-Host ("  {0} {1}" -f $n.Entry.name, $n.Entry.vers) }

# ========================================================== main: download ====

New-Item -ItemType Directory -Force -Path $OutDir | Out-Null
$OutDir = (Resolve-Path $OutDir).Path
$srcDir = Join-Path $OutDir 'src'
if ($Extract) { New-Item -ItemType Directory -Force -Path $srcDir | Out-Null }

Write-Host "`nDownloading into $OutDir ..."
$manifest = @()
foreach ($n in $resolved) {
    $e = $n.Entry
    $file = Join-Path $OutDir ("{0}-{1}.crate" -f $e.name, $e.vers)

    $have = (Test-Path $file) -and ((Get-FileHash $file -Algorithm SHA256).Hash -ieq $e.cksum)
    if ($have) {
        Write-Host "  OK  $($e.name) $($e.vers) (already downloaded)"
    }
    else {
        $url = "https://static.crates.io/crates/{0}/{0}-{1}.crate" -f $e.name, $e.vers
        Write-Host "  GET $($e.name) $($e.vers)"
        Invoke-WebRequest -Uri $url -OutFile $file -UseBasicParsing -Headers @{ 'User-Agent' = $UserAgent }
        $h = (Get-FileHash $file -Algorithm SHA256).Hash
        if ($h -ine $e.cksum) {
            Remove-Item $file -Force
            throw "Checksum mismatch for $($e.name) $($e.vers): expected $($e.cksum), got $h"
        }
    }

    if ($Extract) {
        $target = Join-Path $srcDir ("{0}-{1}" -f $e.name, $e.vers)
        if (-not (Test-Path $target)) {
            & tar -xzf $file -C $srcDir
            if ($LASTEXITCODE -ne 0) { throw "tar failed extracting $file" }
        }
    }
    $manifest += [pscustomobject]@{ Name = $e.name; Version = $e.vers; SHA256 = $e.cksum }
}

$manifest | Export-Csv -NoTypeInformation -Path (Join-Path $OutDir 'crates.csv')
Write-Host ("`nDone. {0} crates in {1}" -f $manifest.Count, $OutDir)
Write-Host "Manifest: $(Join-Path $OutDir 'crates.csv')"
