param(
  [Parameter(Mandatory = $true)][string]$Archive,
  [Parameter(Mandatory = $true)][string]$Destination
)

$ErrorActionPreference = 'Stop'
$expectedArchive = '950B83A0421D50CC7CF669BB610ED48FBCE263EC196B01B51B7C963B95044426'
$expectedCanonical = 'EA721D74A705970208613A91530C4D0248DC8D3C44B32674FEEBD7E2884A962C'
$expectedStored = 'EA8D18383286F9EABF834CC8AAD2605845FA2F575E8EB9130EDE6FFC09C6C3BF'
$expectedSource = '4778206bb3523dda5cbcb56cfee93d9492d61c92'
$expectedMathlib = '07642720480157414db592fa85b626dafb71355b'
$expectedToolchain = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
$expectedRunner = 'cmp89-neumann-finite-depth-physical-poincare-cold-v1'
$expectedStages = @(
  'download_toolchain', 'apt_update', 'install_zstd', 'extract_toolchain',
  'lean_version', 'lake_version', 'clone', 'checkout', 'head',
  'overlay_text_guard', 'import_prefix_guard', 'lake_update', 'mathlib_pin',
  'cache_get', 'finite_depth_physical_poincare_focal',
  'finite_depth_physical_poincare_audit'
)
$expectedBlobs = @{
  'YangMills/RG/BalabanCMP89SourceNeumannFiniteDepthPhysicalPoincare.lean' =
    '4576b6b05de5839185abc0f116a376f3a82b3444aaa7b3013d3e755108f04d03'
  'YangMills/RG/BalabanCMP89SourceNeumannFiniteDepthPhysicalPoincareAudit.lean' =
    'c1d688409943e2d9942ec588ff07799da45116f0b8acd87fb5623e962a6d32d4'
}

$archiveHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $Archive).Hash
if ($archiveHash -ne $expectedArchive) {
  throw "ARCHIVE_HASH_MISMATCH expected=$expectedArchive measured=$archiveHash"
}
if (Test-Path -LiteralPath $Destination) { throw "DESTINATION_ALREADY_EXISTS=$Destination" }
New-Item -ItemType Directory -Path $Destination | Out-Null
tar -xzf $Archive -C $Destination
if ($LASTEXITCODE -ne 0) { throw "ARCHIVE_EXTRACT_FAILED exit=$LASTEXITCODE" }
$evidence = Get-ChildItem -LiteralPath $Destination -Recurse -File -Filter 'evidence.json' |
  Select-Object -First 1
if (-not $evidence) { throw 'EVIDENCE_JSON_MISSING' }
$storedHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $evidence.FullName).Hash
if ($storedHash -ne $expectedStored) {
  throw "STORED_EVIDENCE_HASH_MISMATCH expected=$expectedStored measured=$storedHash"
}
$raw = Get-Content -Raw -LiteralPath $evidence.FullName
$canonical = $raw.TrimEnd([char]13, [char]10)
$sha = [System.Security.Cryptography.SHA256]::Create()
try {
  $canonicalHash = [BitConverter]::ToString(
    $sha.ComputeHash([Text.Encoding]::UTF8.GetBytes($canonical))).Replace('-', '')
} finally {
  $sha.Dispose()
}
if ($canonicalHash -ne $expectedCanonical) {
  throw "CANONICAL_EVIDENCE_HASH_MISMATCH expected=$expectedCanonical measured=$canonicalHash"
}
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
  if ($payload.source_blobs.$path -ne $expectedBlobs[$path]) {
    throw "SOURCE_BLOB_MISMATCH path=$path actual=$($payload.source_blobs.$path)"
  }
}

Write-Output 'CMP89_NEUMANN_FINITE_DEPTH_PHYSICAL_POINCARE_COLD_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$archiveHash"
Write-Output "CANONICAL_EVIDENCE_SHA256=$canonicalHash"
Write-Output "STORED_EVIDENCE_JSON_SHA256=$storedHash"
Write-Output "RECORD_COUNT=$(@($payload.records).Count)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
