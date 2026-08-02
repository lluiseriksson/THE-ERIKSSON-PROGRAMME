[CmdletBinding()]
param(
    [Parameter(Mandatory = $true)]
    [ValidateSet('normal', 'optimized')]
    [string] $Mode,

    [Parameter(Mandatory = $true)]
    [string] $RunDirectory,

    [Parameter(Mandatory = $true)]
    [string] $RepoRoot
)

$ErrorActionPreference = 'Stop'
$python = 'C:\Python312\python.exe'
$judgeRelative = 'scripts/judge_spatial_symweighted_factorization.py'
$judgePath = Join-Path $RepoRoot $judgeRelative
$utf8NoBom = New-Object System.Text.UTF8Encoding($false)

function Get-Sha256DotNet([string] $Path) {
    $stream = [IO.File]::OpenRead($Path)
    $sha = [Security.Cryptography.SHA256]::Create()
    try {
        $bytes = $sha.ComputeHash($stream)
        return ([BitConverter]::ToString($bytes)).Replace('-', '').ToLowerInvariant()
    } finally {
        $sha.Dispose()
        $stream.Dispose()
    }
}

if (-not (Test-Path -LiteralPath $RepoRoot -PathType Container)) {
    throw "repository root does not exist: $RepoRoot"
}
if (-not (Test-Path -LiteralPath $judgePath -PathType Leaf)) {
    throw "judge does not exist: $judgePath"
}
if (-not (Test-Path -LiteralPath $RunDirectory -PathType Container)) {
    throw "run directory does not exist: $RunDirectory"
}

$stdoutPath = Join-Path $RunDirectory "$Mode.log"
$stderrPath = Join-Path $RunDirectory "$Mode.stderr.log"
$exitTmpPath = Join-Path $RunDirectory "$Mode.exitcode.tmp"
$exitFinalPath = Join-Path $RunDirectory "$Mode.exitcode"
$metadataTmpPath = Join-Path $RunDirectory "$Mode.metadata.tmp"
$metadataFinalPath = Join-Path $RunDirectory "$Mode.metadata.json"
$failurePath = Join-Path $RunDirectory "$Mode.wrapper.failure.log"

foreach ($path in @(
    $stdoutPath, $stderrPath, $exitTmpPath, $exitFinalPath,
    $metadataTmpPath, $metadataFinalPath, $failurePath
)) {
    if (Test-Path -LiteralPath $path) {
        throw "refusing to reuse mode output: $path"
    }
}

try {
    $arguments = if ($Mode -eq 'optimized') {
        @('-O', $judgeRelative)
    } else {
        @($judgeRelative)
    }

    $started = [DateTimeOffset]::Now
    $child = Start-Process -FilePath $python -ArgumentList $arguments `
        -WorkingDirectory $RepoRoot -WindowStyle Hidden `
        -RedirectStandardOutput $stdoutPath -RedirectStandardError $stderrPath `
        -PassThru
    $child.WaitForExit()
    $exitCode = [int] $child.ExitCode
    $completed = [DateTimeOffset]::Now

    $metadata = [ordered]@{
        mode = $Mode
        wrapper_pid = $PID
        child_pid = $child.Id
        exit_code = $exitCode
        started = $started.ToString('o')
        completed = $completed.ToString('o')
        wall_seconds = ($completed - $started).TotalSeconds
        command = @($python) + $arguments
        stdout_bytes = (Get-Item -LiteralPath $stdoutPath).Length
        stderr_bytes = (Get-Item -LiteralPath $stderrPath).Length
        stdout_sha256 = Get-Sha256DotNet $stdoutPath
        stderr_sha256 = Get-Sha256DotNet $stderrPath
        judge_sha256 = Get-Sha256DotNet $judgePath
    } | ConvertTo-Json -Compress
    [IO.File]::WriteAllText(
        $metadataTmpPath,
        $metadata + [Environment]::NewLine,
        $utf8NoBom
    )
    if ((Get-Item -LiteralPath $metadataTmpPath).Length -le 0) {
        throw 'empty metadata tmp'
    }
    [IO.File]::Move($metadataTmpPath, $metadataFinalPath)

    # The final sentinel contains exactly one line: the child's decimal exit
    # code.  Metadata never enters this file.
    [IO.File]::WriteAllText(
        $exitTmpPath,
        $exitCode.ToString([Globalization.CultureInfo]::InvariantCulture) +
            [Environment]::NewLine,
        $utf8NoBom
    )
    if ((Get-Item -LiteralPath $exitTmpPath).Length -le 0) {
        throw 'empty exit-code tmp'
    }
    $lines = [IO.File]::ReadAllLines($exitTmpPath)
    $parsed = 0
    if ($lines.Length -ne 1 -or
        -not [int]::TryParse(
            $lines[0],
            [Globalization.NumberStyles]::Integer,
            [Globalization.CultureInfo]::InvariantCulture,
            [ref] $parsed
        ) -or $parsed -ne $exitCode) {
        throw 'exit-code tmp is not exactly one matching decimal line'
    }
    [IO.File]::Move($exitTmpPath, $exitFinalPath)
    exit $exitCode
} catch {
    [IO.File]::WriteAllText($failurePath, ($_ | Out-String), $utf8NoBom)
    exit 97
}
