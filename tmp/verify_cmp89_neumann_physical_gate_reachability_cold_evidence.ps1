param(
  [Parameter(Mandatory = $true)][string]$Archive,
  [Parameter(Mandatory = $true)][string]$ExpectedArchiveSha256,
  [Parameter(Mandatory = $true)][string]$ExpectedCanonicalEvidenceSha256,
  [Parameter(Mandatory = $true)][string]$Destination
)

$ErrorActionPreference = 'Stop'
$expectedSource = 'b85e7f8a401e82971889eebe50b5a10875c2046b'
$expectedMathlib = '07642720480157414db592fa85b626dafb71355b'
$expectedToolchain = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
$expectedRunner = 'cmp89-neumann-physical-gate-reachability-cold-v1'
$expectedStages = @(
  'physical_gate_monotonicity_focal',
  'physical_gate_monotonicity_audit',
  'physical_gate_reachability_focal',
  'physical_gate_reachability_audit'
)

$measuredArchive = (Get-FileHash -Algorithm SHA256 -LiteralPath $Archive).Hash
if ($measuredArchive -ne $ExpectedArchiveSha256.ToUpperInvariant()) {
  throw "ARCHIVE_HASH_MISMATCH expected=$ExpectedArchiveSha256 measured=$measuredArchive"
}
if (Test-Path -LiteralPath $Destination) {
  throw "DESTINATION_ALREADY_EXISTS=$Destination"
}
New-Item -ItemType Directory -Path $Destination | Out-Null
tar -xzf $Archive -C $Destination
if ($LASTEXITCODE -ne 0) { throw "ARCHIVE_EXTRACT_FAILED exit=$LASTEXITCODE" }

$evidence = Get-ChildItem -LiteralPath $Destination -Recurse -File -Filter 'evidence.json' |
  Select-Object -First 1
if (-not $evidence) { throw 'EVIDENCE_JSON_MISSING' }
$raw = Get-Content -Raw -LiteralPath $evidence.FullName
$canonical = $raw.TrimEnd([char]13, [char]10)
$sha = [System.Security.Cryptography.SHA256]::Create()
try {
  $canonicalHash = [Convert]::ToHexString(
    $sha.ComputeHash([Text.Encoding]::UTF8.GetBytes($canonical)))
} finally {
  $sha.Dispose()
}
if ($canonicalHash -ne $ExpectedCanonicalEvidenceSha256.ToUpperInvariant()) {
  throw "CANONICAL_EVIDENCE_HASH_MISMATCH expected=$ExpectedCanonicalEvidenceSha256 measured=$canonicalHash"
}
$storedHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $evidence.FullName).Hash
$payload = $raw | ConvertFrom-Json
if ($payload.status -ne 'PASS') { throw "EVIDENCE_STATUS_NOT_PASS=$($payload.status)" }
if ($payload.runner_rev -ne $expectedRunner) { throw "RUNNER_REV_MISMATCH=$($payload.runner_rev)" }
if ($payload.source_sha -ne $expectedSource) { throw "SOURCE_SHA_MISMATCH=$($payload.source_sha)" }
if ($payload.mathlib_sha -ne $expectedMathlib) { throw "MATHLIB_SHA_MISMATCH=$($payload.mathlib_sha)" }
if ($payload.toolchain_asset_sha256 -ne $expectedToolchain) {
  throw "TOOLCHAIN_SHA_MISMATCH=$($payload.toolchain_asset_sha256)"
}
if (@($payload.source_blobs.psobject.Properties).Count -ne 4) {
  throw "SOURCE_BLOB_COUNT_MISMATCH=$(@($payload.source_blobs.psobject.Properties).Count)"
}
foreach ($stage in $expectedStages) {
  $records = @($payload.records | Where-Object { $_.stage -eq $stage })
  if ($records.Count -ne 1 -or [int]$records[0].exit -ne 0) {
    throw "STAGE_RECORD_INVALID=$stage"
  }
}
foreach ($record in @($payload.records)) {
  if ([int]$record.exit -ne 0) { throw "NONZERO_RECORD=$($record.stage)" }
}

Write-Output 'CMP89_NEUMANN_PHYSICAL_GATE_REACHABILITY_COLD_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$measuredArchive"
Write-Output "CANONICAL_EVIDENCE_SHA256=$canonicalHash"
Write-Output "STORED_EVIDENCE_JSON_SHA256=$storedHash"
Write-Output "RECORD_COUNT=$(@($payload.records).Count)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
