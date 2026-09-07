param(
  [Parameter(Mandatory = $true)][string]$Archive,
  [Parameter(Mandatory = $true)][string]$Destination
)

$ErrorActionPreference = 'Stop'
$expectedArchive = 'C4FDFBD6065A5B8CE493FEAC31F7822BD4BBC34F27098067953C96A33FDDF61C'
$expectedCanonical = '4DCDA52D14907988470324528932F01DA5E83234737D4081DEFE923A32A588A0'
$expectedStored = 'D05A7FBFD3FAB0DCAFBC74F4EA3C0F8DD4A157FFA381F54F536ADB241BF15E0E'
$expectedSource = '0900460f6c2b00e4a86b4797090f66078a9c5ad3'
$expectedMathlib = '07642720480157414db592fa85b626dafb71355b'
$expectedToolchain = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
$expectedRunner = 'cmp89-neumann-rectangle-active-region-cold-v1'
$expectedStages = @(
  'download_toolchain', 'extract_toolchain', 'lean_version', 'lake_version',
  'clone', 'checkout', 'head', 'overlay_text_guard', 'import_prefix_guard',
  'lake_update', 'mathlib_pin', 'cache_get',
  'neumann_rectangle_active_region_focal',
  'neumann_rectangle_active_region_audit'
)
$expectedBlobs = @{
  'YangMills/RG/BalabanCMP89NeumannRectangleActiveRegion.lean' =
    '0676842b0f2aae4b2b17da1c561d3eca603400c00830361c35dc92d6faee2137'
  'YangMills/RG/BalabanCMP89NeumannRectangleActiveRegionAudit.lean' =
    '7918288ee8bb0ab23b5cab6389f903797d0010e2912b988d5c7990395c313f3c'
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

Write-Output 'CMP89_NEUMANN_RECTANGLE_ACTIVE_REGION_COLD_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$archiveHash"
Write-Output "CANONICAL_EVIDENCE_SHA256=$canonicalHash"
Write-Output "STORED_EVIDENCE_JSON_SHA256=$storedHash"
Write-Output "RECORD_COUNT=$(@($payload.records).Count)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
