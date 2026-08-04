[CmdletBinding()]
param(
    [Parameter()]
    [string]$RepositoryRoot = (Split-Path -Parent $PSScriptRoot),

    [Parameter()]
    [string]$PackagesRoot,

    [Parameter()]
    [ValidateRange(1, 3600)]
    [int]$FsckTimeoutSeconds = 600,

    [Parameter()]
    [string]$ExpectedToolchain = 'leanprover/lean4:v4.29.0-rc6',

    [Parameter()]
    [string]$ExpectedMathlibCommit = '07642720480157414db592fa85b626dafb71355b',

    [Parameter()]
    [string[]]$AllowNoOleanPackage = @('Cli'),

    [Parameter()]
    [switch]$SkipFsck,

    [Parameter()]
    [switch]$Json,

    [Parameter()]
    [switch]$SelfTest
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

function Test-IsReparsePoint {
    param([Parameter(Mandatory)][System.IO.FileSystemInfo]$Item)
    return [bool]($Item.Attributes -band [System.IO.FileAttributes]::ReparsePoint)
}

function Invoke-GitReadOnly {
    param(
        [Parameter(Mandatory)][string]$WorkingDirectory,
        [Parameter(Mandatory)][string[]]$Arguments,
        [Parameter(Mandatory)][int]$TimeoutSeconds
    )

    $startInfo = [System.Diagnostics.ProcessStartInfo]::new()
    $startInfo.FileName = 'git'
    $startInfo.WorkingDirectory = $WorkingDirectory
    $startInfo.UseShellExecute = $false
    $startInfo.RedirectStandardOutput = $true
    $startInfo.RedirectStandardError = $true
    $startInfo.CreateNoWindow = $true
    foreach ($argument in $Arguments) {
        [void]$startInfo.ArgumentList.Add($argument)
    }

    $process = [System.Diagnostics.Process]::new()
    $process.StartInfo = $startInfo
    $startedAt = [System.Diagnostics.Stopwatch]::StartNew()
    if (-not $process.Start()) {
        return [pscustomobject]@{
            ExitCode = -1
            TimedOut = $false
            ElapsedSeconds = 0
            Stdout = ''
            Stderr = 'git process did not start'
        }
    }

    $stdoutTask = $process.StandardOutput.ReadToEndAsync()
    $stderrTask = $process.StandardError.ReadToEndAsync()
    $finished = $process.WaitForExit($TimeoutSeconds * 1000)
    if (-not $finished) {
        # This kills only the git process created by this function.
        $process.Kill($true)
        $process.WaitForExit()
    }
    $startedAt.Stop()

    return [pscustomobject]@{
        ExitCode = if ($finished) { $process.ExitCode } else { 124 }
        TimedOut = -not $finished
        ElapsedSeconds = [math]::Round($startedAt.Elapsed.TotalSeconds, 3)
        Stdout = $stdoutTask.GetAwaiter().GetResult().TrimEnd()
        Stderr = $stderrTask.GetAwaiter().GetResult().TrimEnd()
    }
}

function Get-FileCountWithoutFollowingReparsePoints {
    param(
        [Parameter(Mandatory)][string]$Root,
        [Parameter(Mandatory)][string]$Pattern
    )

    $options = [System.IO.EnumerationOptions]::new()
    $options.RecurseSubdirectories = $true
    $options.IgnoreInaccessible = $false
    $options.AttributesToSkip = [System.IO.FileAttributes]::ReparsePoint
    $count = 0
    foreach ($unused in [System.IO.Directory]::EnumerateFiles($Root, $Pattern, $options)) {
        $count += 1
    }
    return $count
}

function Get-ReparsePointSummaryWithoutFollowing {
    param([Parameter(Mandatory)][string]$Root)

    $pending = [System.Collections.Generic.Stack[string]]::new()
    $pending.Push($Root)
    $count = 0
    $samples = [System.Collections.Generic.List[string]]::new()
    $options = [System.IO.EnumerationOptions]::new()
    $options.RecurseSubdirectories = $false
    $options.IgnoreInaccessible = $false
    $options.ReturnSpecialDirectories = $false
    $options.AttributesToSkip = [System.IO.FileAttributes]0

    while ($pending.Count -gt 0) {
        $directory = [System.IO.DirectoryInfo]::new($pending.Pop())
        foreach ($entry in $directory.EnumerateFileSystemInfos('*', $options)) {
            $isReparse = [bool]($entry.Attributes -band [System.IO.FileAttributes]::ReparsePoint)
            if ($isReparse) {
                $count += 1
                if ($samples.Count -lt 5) { $samples.Add($entry.FullName) }
                continue
            }
            if ([bool]($entry.Attributes -band [System.IO.FileAttributes]::Directory)) {
                $pending.Push($entry.FullName)
            }
        }
    }

    return [pscustomobject]@{ Count = $count; Sample = @($samples) }
}

function Normalize-GitUrl {
    param([AllowEmptyString()][string]$Url)
    return (($Url.Trim() -replace '\\.git$', '') -replace '/$', '').ToLowerInvariant()
}

function Get-RecordFailures {
    param(
        [Parameter(Mandatory)]$Record,
        [Parameter(Mandatory)][string[]]$AllowedWithoutOlean
    )

    $failures = [System.Collections.Generic.List[string]]::new()
    if (-not $Record.Exists) { $failures.Add('package-missing') }
    if ($Record.ReparsePoint) { $failures.Add('package-reparse-point') }
    if ($Record.ReparsePointCount -gt 0) { $failures.Add('nested-reparse-point') }
    if ($Record.DotGitReparsePoint) { $failures.Add('dotgit-reparse-point') }
    if ($Record.DotGitType -eq 'missing') { $failures.Add('dotgit-missing') }
    if ($Record.HeadExitCode -ne 0 -or [string]::IsNullOrWhiteSpace($Record.Head)) {
        $failures.Add('head-unresolvable')
    }
    if ($Record.HeadExitCode -eq 0 -and $Record.Head -ne $Record.ExpectedCommit) {
        $failures.Add('pin-divergence')
    }
    if (-not $Record.ExpectedObjectPresent) { $failures.Add('expected-object-missing') }
    if ($Record.StatusExitCode -ne 0) { $failures.Add('status-failed') }
    if ($Record.StatusCount -gt 0) { $failures.Add('tracked-files-dirty') }
    if ($null -ne $Record.FsckExitCode -and $Record.FsckExitCode -ne 0) {
        $failures.Add('fsck-bad-or-timeout')
    }
    if ($Record.LockCount -gt 0) { $failures.Add('git-lock-present') }
    if ($Record.OleanCount -eq 0 -and $Record.Name -notin $AllowedWithoutOlean) {
        $failures.Add('olean-absent')
    }
    if ((Normalize-GitUrl $Record.Origin) -ne (Normalize-GitUrl $Record.ExpectedUrl)) {
        $failures.Add('origin-divergence')
    }
    return @($failures)
}

function Invoke-MutationSelfTest {
    $base = [ordered]@{
        Name = 'mathlib'
        Exists = $true
        ReparsePoint = $false
        ReparsePointCount = 0
        DotGitReparsePoint = $false
        DotGitType = 'directory'
        HeadExitCode = 0
        Head = 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa'
        ExpectedCommit = 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa'
        ExpectedObjectPresent = $true
        StatusExitCode = 0
        StatusCount = 0
        FsckExitCode = 0
        LockCount = 0
        OleanCount = 1
        Origin = 'https://example.invalid/mathlib.git'
        ExpectedUrl = 'https://example.invalid/mathlib.git'
    }

    $cases = @(
        @{ Name = 'clean-control'; Mutate = @{}; Expected = @() },
        @{ Name = 'unresolvable-head'; Mutate = @{ HeadExitCode = 128; Head = '' }; Expected = @('head-unresolvable') },
        @{ Name = 'pin-divergence'; Mutate = @{ Head = 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb' }; Expected = @('pin-divergence') },
        @{ Name = 'reparse-point'; Mutate = @{ ReparsePoint = $true }; Expected = @('package-reparse-point') },
        @{ Name = 'nested-reparse-point'; Mutate = @{ ReparsePointCount = 1 }; Expected = @('nested-reparse-point') },
        @{ Name = 'fsck-corruption'; Mutate = @{ FsckExitCode = 1 }; Expected = @('fsck-bad-or-timeout') },
        @{ Name = 'missing-olean'; Mutate = @{ OleanCount = 0 }; Expected = @('olean-absent') }
    )

    $errors = [System.Collections.Generic.List[string]]::new()
    foreach ($case in $cases) {
        $candidate = [ordered]@{}
        foreach ($key in $base.Keys) { $candidate[$key] = $base[$key] }
        foreach ($key in $case.Mutate.Keys) { $candidate[$key] = $case.Mutate[$key] }
        $actual = @(Get-RecordFailures ([pscustomobject]$candidate) @('Cli'))
        $expected = @($case.Expected)
        if (($actual -join ',') -ne ($expected -join ',')) {
            $errors.Add("$($case.Name): expected [$($expected -join ',')] but got [$($actual -join ',')]")
        }
    }

    if ($errors.Count -gt 0) {
        foreach ($message in $errors) { [Console]::Error.WriteLine("SELF-TEST ERROR: $message") }
        return $false
    }
    [Console]::Out.WriteLine('SELF-TEST PASS: 6 decisive mutations rejected; clean control accepted')
    return $true
}

if ($SelfTest) {
    if (Invoke-MutationSelfTest) { exit 0 }
    exit 1
}

$resolvedRepositoryRoot = (Resolve-Path -LiteralPath $RepositoryRoot).Path
if ([string]::IsNullOrWhiteSpace($PackagesRoot)) {
    $PackagesRoot = Join-Path $resolvedRepositoryRoot '.lake\packages'
}

$topLevelFailures = [System.Collections.Generic.List[string]]::new()
$manifestPath = Join-Path $resolvedRepositoryRoot 'lake-manifest.json'
$toolchainPath = Join-Path $resolvedRepositoryRoot 'lean-toolchain'
$lakefilePath = Join-Path $resolvedRepositoryRoot 'lakefile.lean'

foreach ($requiredPath in @($manifestPath, $toolchainPath, $lakefilePath)) {
    if (-not (Test-Path -LiteralPath $requiredPath -PathType Leaf)) {
        $topLevelFailures.Add("required-file-missing:$requiredPath")
    }
}
if ($topLevelFailures.Count -gt 0) {
    foreach ($message in $topLevelFailures) { [Console]::Error.WriteLine("ERROR: $message") }
    exit 1
}

$toolchain = (Get-Content -Raw -LiteralPath $toolchainPath).Trim()
if ($toolchain -ne $ExpectedToolchain) {
    $topLevelFailures.Add("toolchain-divergence:$toolchain")
}

$manifest = Get-Content -Raw -LiteralPath $manifestPath | ConvertFrom-Json
$mathlib = @($manifest.packages | Where-Object { $_.name -eq 'mathlib' })
if ($mathlib.Count -ne 1) {
    $topLevelFailures.Add("mathlib-entry-count:$($mathlib.Count)")
} else {
    if ($mathlib[0].rev -ne $ExpectedMathlibCommit) { $topLevelFailures.Add('mathlib-manifest-rev-divergence') }
    if ($mathlib[0].inputRev -ne $ExpectedMathlibCommit) { $topLevelFailures.Add('mathlib-manifest-inputRev-divergence') }
}
$lakefileText = Get-Content -Raw -LiteralPath $lakefilePath
if (-not $lakefileText.Contains($ExpectedMathlibCommit)) {
    $topLevelFailures.Add('mathlib-lakefile-pin-missing')
}

$packageRootItem = Get-Item -LiteralPath $PackagesRoot -Force -ErrorAction SilentlyContinue
if ($null -eq $packageRootItem -or -not $packageRootItem.PSIsContainer) {
    $topLevelFailures.Add("packages-root-missing:$PackagesRoot")
} elseif (Test-IsReparsePoint $packageRootItem) {
    $topLevelFailures.Add("packages-root-reparse-point:$($packageRootItem.FullName)")
}

$records = [System.Collections.Generic.List[object]]::new()
if ($null -ne $packageRootItem -and $packageRootItem.PSIsContainer -and -not (Test-IsReparsePoint $packageRootItem)) {
    foreach ($package in $manifest.packages) {
        $packagePath = Join-Path $packageRootItem.FullName $package.name
        $packageItem = Get-Item -LiteralPath $packagePath -Force -ErrorAction SilentlyContinue
        if ($null -eq $packageItem -or -not $packageItem.PSIsContainer) {
            $records.Add([pscustomobject]@{
                Name = $package.name; ExpectedCommit = $package.rev; ExpectedUrl = $package.url
                Path = $packagePath; Exists = $false; ReparsePoint = $false
                ReparsePointCount = 0; ReparsePointSample = @()
                DotGitType = 'missing'; DotGitReparsePoint = $false
                Head = ''; HeadExitCode = 128; HeadMode = 'invalid'; SymbolicHead = ''
                ExpectedObjectPresent = $false; Origin = ''; RefsCount = 0
                StatusExitCode = 128; StatusCount = 0; StatusSample = ''
                FsckExitCode = if ($SkipFsck) { $null } else { 128 }
                FsckTimedOut = $false; FsckElapsedSeconds = 0; FsckOutput = ''
                Shallow = $false; Alternates = ''; LockCount = 0; OleanCount = 0
            })
            continue
        }

        $dotGitItem = Get-Item -LiteralPath (Join-Path $packagePath '.git') -Force -ErrorAction SilentlyContinue
        $head = Invoke-GitReadOnly $packagePath @('rev-parse', '--verify', 'HEAD^{commit}') 30
        $symbolic = Invoke-GitReadOnly $packagePath @('symbolic-ref', '-q', 'HEAD') 30
        $expectedObject = Invoke-GitReadOnly $packagePath @('cat-file', '-e', "$($package.rev)^{commit}") 30
        $origin = Invoke-GitReadOnly $packagePath @('remote', 'get-url', 'origin') 30
        $refs = Invoke-GitReadOnly $packagePath @('show-ref', '--head') 60
        $status = Invoke-GitReadOnly $packagePath @('status', '--porcelain=v1', '--untracked-files=no') 60
        $gitDirectoryResult = Invoke-GitReadOnly $packagePath @('rev-parse', '--absolute-git-dir') 30
        $gitDirectory = if ($gitDirectoryResult.ExitCode -eq 0) { $gitDirectoryResult.Stdout } else { '' }
        $shallow = $false
        $alternates = ''
        $lockCount = 0
        if (-not [string]::IsNullOrWhiteSpace($gitDirectory) -and (Test-Path -LiteralPath $gitDirectory)) {
            $shallow = Test-Path -LiteralPath (Join-Path $gitDirectory 'shallow')
            $alternatesPath = Join-Path $gitDirectory 'objects\info\alternates'
            if (Test-Path -LiteralPath $alternatesPath -PathType Leaf) {
                $alternates = (Get-Content -Raw -LiteralPath $alternatesPath).Trim()
            }
            $lockCount = Get-FileCountWithoutFollowingReparsePoints $gitDirectory '*.lock'
        }
        $oleanCount = Get-FileCountWithoutFollowingReparsePoints $packagePath '*.olean'
        $reparseSummary = Get-ReparsePointSummaryWithoutFollowing $packagePath

        $fsck = if ($SkipFsck) {
            $null
        } else {
            Invoke-GitReadOnly $packagePath @('fsck', '--full', '--no-progress') $FsckTimeoutSeconds
        }

        $record = [pscustomobject]@{
            Name = $package.name
            ExpectedCommit = $package.rev
            ExpectedUrl = $package.url
            Path = $packageItem.FullName
            Exists = $true
            ReparsePoint = Test-IsReparsePoint $packageItem
            ReparsePointCount = $reparseSummary.Count
            ReparsePointSample = @($reparseSummary.Sample)
            DotGitType = if ($null -eq $dotGitItem) { 'missing' } elseif ($dotGitItem.PSIsContainer) { 'directory' } else { 'file' }
            DotGitReparsePoint = if ($null -eq $dotGitItem) { $false } else { Test-IsReparsePoint $dotGitItem }
            Head = $head.Stdout
            HeadExitCode = $head.ExitCode
            HeadMode = if ($symbolic.ExitCode -eq 0) { 'symbolic' } elseif ($head.ExitCode -eq 0) { 'detached' } else { 'invalid' }
            SymbolicHead = if ($symbolic.ExitCode -eq 0) { $symbolic.Stdout } else { '' }
            ExpectedObjectPresent = $expectedObject.ExitCode -eq 0
            Origin = $origin.Stdout
            RefsCount = if ([string]::IsNullOrWhiteSpace($refs.Stdout)) { 0 } else { @($refs.Stdout -split "`r?`n").Count }
            StatusExitCode = $status.ExitCode
            StatusCount = if ([string]::IsNullOrWhiteSpace($status.Stdout)) { 0 } else { @($status.Stdout -split "`r?`n").Count }
            StatusSample = @($status.Stdout -split "`r?`n" | Select-Object -First 5) -join "`n"
            FsckExitCode = if ($null -eq $fsck) { $null } else { $fsck.ExitCode }
            FsckTimedOut = if ($null -eq $fsck) { $false } else { $fsck.TimedOut }
            FsckElapsedSeconds = if ($null -eq $fsck) { 0 } else { $fsck.ElapsedSeconds }
            FsckOutput = if ($null -eq $fsck) { 'SKIPPED' } else { (@($fsck.Stdout, $fsck.Stderr) | Where-Object { $_ }) -join "`n" }
            Shallow = $shallow
            Alternates = $alternates
            LockCount = $lockCount
            OleanCount = $oleanCount
        }
        $records.Add($record)
    }
}

$packageFailures = [System.Collections.Generic.List[object]]::new()
foreach ($record in $records) {
    $failures = @(Get-RecordFailures $record $AllowNoOleanPackage)
    if ($failures.Count -gt 0) {
        $packageFailures.Add([pscustomobject]@{ Name = $record.Name; Failures = $failures })
    }
}

$report = [pscustomobject]@{
    SchemaVersion = 1
    CheckedAtUtc = [DateTime]::UtcNow.ToString('o')
    RepositoryRoot = $resolvedRepositoryRoot
    PackagesRoot = $PackagesRoot
    Toolchain = $toolchain
    ExpectedToolchain = $ExpectedToolchain
    ExpectedMathlibCommit = $ExpectedMathlibCommit
    FsckSkipped = [bool]$SkipFsck
    TopLevelFailures = @($topLevelFailures)
    PackageFailures = @($packageFailures)
    Packages = @($records)
    Healthy = $topLevelFailures.Count -eq 0 -and $packageFailures.Count -eq 0
}

if ($Json) {
    $report | ConvertTo-Json -Depth 8
} else {
    Write-Output "Lean environment health: $(if ($report.Healthy) { 'PASS' } else { 'FAIL' })"
    Write-Output "repository=$($report.RepositoryRoot)"
    Write-Output "packages=$($report.PackagesRoot)"
    Write-Output "toolchain=$($report.Toolchain)"
    foreach ($record in $records) {
        Write-Output ("package={0} head={1} expected={2} git={3} mode={4} refs={5} status={6} fsck={7} shallow={8} alternates={9} locks={10} oleans={11} reparse={12} nestedReparse={13}" -f
            $record.Name, $record.Head, $record.ExpectedCommit, $record.DotGitType,
            $record.HeadMode, $record.RefsCount, $record.StatusCount,
            $record.FsckExitCode, $record.Shallow,
            (-not [string]::IsNullOrWhiteSpace($record.Alternates)),
            $record.LockCount, $record.OleanCount, $record.ReparsePoint,
            $record.ReparsePointCount)
    }
    foreach ($failure in $topLevelFailures) { [Console]::Error.WriteLine("ERROR: $failure") }
    foreach ($failure in $packageFailures) {
        [Console]::Error.WriteLine("ERROR: package=$($failure.Name) failures=$($failure.Failures -join ',')")
    }
}

if ($report.Healthy) { exit 0 }
exit 1
