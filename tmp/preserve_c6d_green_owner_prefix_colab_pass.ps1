param(
  [Parameter(Mandatory = $true)]
  [string]$Archive,

  [Parameter(Mandatory = $true)]
  [string]$ExecutedNotebook
)

$ErrorActionPreference = 'Stop'

$Repo = Split-Path -Parent $PSScriptRoot
$SourceSha = '86d9f0e44a17e6f80667257e4ecfd814a67adaed'
$ExpectedSentinel = 'C6D_GREEN_OWNER_PREFIX_EVIDENCE_OK'
$Destination = Join-Path $Repo 'validation-evidence\c6d-green-owner-prefix-pass-86d9f0e4-20260829'
$Verifier = Join-Path $Repo 'tmp\verify_c6d_green_owner_prefix_evidence.py'

foreach ($Path in @($Archive, $ExecutedNotebook, $Verifier)) {
  if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
    throw "Required file is missing: $Path"
  }
}

$ArchiveItem = Get-Item -LiteralPath $Archive
$NotebookItem = Get-Item -LiteralPath $ExecutedNotebook
$ArchiveSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $ArchiveItem.FullName).Hash
$NotebookSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $NotebookItem.FullName).Hash

New-Item -ItemType Directory -Path $Destination -Force | Out-Null
$ArchiveDest = Join-Path $Destination $ArchiveItem.Name
$NotebookDest = Join-Path $Destination $NotebookItem.Name

foreach ($Copy in @(
  @{ Source = $ArchiveItem.FullName; Destination = $ArchiveDest; Sha = $ArchiveSha },
  @{ Source = $NotebookItem.FullName; Destination = $NotebookDest; Sha = $NotebookSha }
)) {
  if (Test-Path -LiteralPath $Copy.Destination -PathType Leaf) {
    $ExistingSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $Copy.Destination).Hash
    if ($ExistingSha -ne $Copy.Sha) {
      throw "Destination collision with different bytes: $($Copy.Destination)"
    }
  } else {
    Copy-Item -LiteralPath $Copy.Source -Destination $Copy.Destination
  }
  $CopiedSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $Copy.Destination).Hash
  if ($CopiedSha -ne $Copy.Sha) {
    throw "Post-copy hash mismatch: $($Copy.Destination)"
  }
}

$VerifierOutput = & python $Verifier $ArchiveDest $NotebookDest 2>&1
$VerifierExit = $LASTEXITCODE
$VerifierText = ($VerifierOutput | Out-String)
$VerifierText
if ($VerifierExit -ne 0) {
  throw "Evidence verifier failed with exit code $VerifierExit"
}
if ($VerifierText -notmatch [regex]::Escape($ExpectedSentinel)) {
  throw "Evidence verifier omitted sentinel $ExpectedSentinel"
}

$Checksums = @(
  "$ArchiveSha  $($ArchiveItem.Name)",
  "$NotebookSha  $($NotebookItem.Name)"
)
$ChecksumsPath = Join-Path $Destination 'CHECKSUMS.sha256'
[IO.File]::WriteAllLines($ChecksumsPath, $Checksums, [Text.UTF8Encoding]::new($false))

Write-Output 'C6D_GREEN_OWNER_PREFIX_PASS_PRESERVED=1'
Write-Output "SOURCE_SHA=$SourceSha"
Write-Output "ARCHIVE_SHA256=$ArchiveSha"
Write-Output "NOTEBOOK_SHA256=$NotebookSha"
Write-Output "DESTINATION=$Destination"
