param(
  [Parameter(Mandatory = $true)]
  [string]$Archive,

  [Parameter(Mandatory = $true)]
  [string]$ExecutedNotebook
)

$ErrorActionPreference = 'Stop'

$Repo = Split-Path -Parent $PSScriptRoot
$SourceSha = '1d7b33059eb3964a3ff99003869be84ec0806288'
$FailureArchiveSha = 'E8FC2A70CE901ADF03CB8E5668F72E023DCA08B3B23CC709F4EFFCAE1ECAB714'
$FailureNotebookSha = 'A50C57FB453FADE9CFFDDD015A35E314707679217F2ED21D0210AB0700C00C38'
$ExpectedSentinel = 'C6D_D2_OWNER_RESCALING_EVIDENCE_OK'
$Destination = Join-Path $Repo 'validation-evidence\c6d-d2-owner-rescaling-pass-1d7b3305-20260829'
$Verifier = Join-Path $Repo 'tmp\verify_c6d_exact_green_decay_owner_rescaling_evidence.py'

foreach ($Path in @($Archive, $ExecutedNotebook, $Verifier)) {
  if (-not (Test-Path -LiteralPath $Path -PathType Leaf)) {
    throw "Required file is missing: $Path"
  }
}

$ArchiveItem = Get-Item -LiteralPath $Archive
$NotebookItem = Get-Item -LiteralPath $ExecutedNotebook
$ArchiveSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $ArchiveItem.FullName).Hash
$NotebookSha = (Get-FileHash -Algorithm SHA256 -LiteralPath $NotebookItem.FullName).Hash

if ($ArchiveSha -eq $FailureArchiveSha) {
  throw 'Refusing the retained v1 failure archive.'
}
if ($NotebookSha -eq $FailureNotebookSha) {
  throw 'Refusing the retained v1 failure notebook.'
}

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

Write-Output 'C6D_D2_OWNER_RESCALING_PASS_PRESERVED=1'
Write-Output "SOURCE_SHA=$SourceSha"
Write-Output "ARCHIVE_SHA256=$ArchiveSha"
Write-Output "NOTEBOOK_SHA256=$NotebookSha"
Write-Output "DESTINATION=$Destination"
