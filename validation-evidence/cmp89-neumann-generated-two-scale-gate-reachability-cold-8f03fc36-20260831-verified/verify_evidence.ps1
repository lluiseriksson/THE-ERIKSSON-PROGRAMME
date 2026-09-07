param(
  [Parameter(Mandatory = $true)][string]$Archive,
  [Parameter(Mandatory = $true)][string]$ExpectedArchiveSha256,
  [Parameter(Mandatory = $true)][string]$ExpectedCanonicalEvidenceSha256,
  [Parameter(Mandatory = $true)][string]$Destination
)

$ErrorActionPreference = 'Stop'
$expectedSource = '8f03fc36022487e7fff32a2989055ad36b628de2'
$expectedMathlib = '07642720480157414db592fa85b626dafb71355b'
$expectedToolchain = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
$expectedRunner = 'cmp89-neumann-generated-two-scale-gate-reachability-cold-v1'
$expectedStages = @(
  'download_toolchain',
  'extract_toolchain',
  'lean_version',
  'lake_version',
  'clone',
  'checkout',
  'head',
  'overlay_text_guard',
  'import_prefix_guard',
  'lake_update',
  'mathlib_pin',
  'cache_get',
  'generated_two_scale_gate_focal',
  'generated_two_scale_gate_audit'
)
$expectedBlobs = @{
  'YangMills/RG/BalabanCMP89SourceNeumannGeneratedTwoScaleGateReachability.lean' =
    'de78a88541358ee9b670bf78046af3cbda7764e2e6edaa48ef21a6bfe3fb5217'
  'YangMills/RG/BalabanCMP89SourceNeumannGeneratedTwoScaleGateReachabilityAudit.lean' =
    '0aa92987547320ac94f94fd1afeaee5f528a1ce4027a0af446ec4b51698995a6'
}

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
  $canonicalHash = [BitConverter]::ToString(
    $sha.ComputeHash([Text.Encoding]::UTF8.GetBytes($canonical))).Replace('-', '')
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
if (@($payload.records).Count -ne $expectedStages.Count) {
  throw "RECORD_COUNT_MISMATCH=$(@($payload.records).Count)"
}
for ($i = 0; $i -lt $expectedStages.Count; $i++) {
  $record = @($payload.records)[$i]
  if ($record.stage -ne $expectedStages[$i] -or [int]$record.exit -ne 0) {
    throw "STAGE_RECORD_INVALID index=$i stage=$($record.stage) exit=$($record.exit)"
  }
}
$blobProperties = @($payload.source_blobs.psobject.Properties)
if ($blobProperties.Count -ne $expectedBlobs.Count) {
  throw "SOURCE_BLOB_COUNT_MISMATCH=$($blobProperties.Count)"
}
foreach ($path in $expectedBlobs.Keys) {
  $actual = $payload.source_blobs.$path
  if ($actual -ne $expectedBlobs[$path]) {
    throw "SOURCE_BLOB_MISMATCH path=$path actual=$actual"
  }
}

Write-Output 'CMP89_NEUMANN_GENERATED_TWO_SCALE_GATE_REACHABILITY_COLD_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$measuredArchive"
Write-Output "CANONICAL_EVIDENCE_SHA256=$canonicalHash"
Write-Output "STORED_EVIDENCE_JSON_SHA256=$storedHash"
Write-Output "RECORD_COUNT=$(@($payload.records).Count)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
