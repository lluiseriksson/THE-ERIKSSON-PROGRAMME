param(
  [Parameter(Mandatory = $true)][string]$Archive,
  [Parameter(Mandatory = $true)][string]$Destination
)

$ErrorActionPreference = 'Stop'
$expectedArchive = 'E0BD84A5B470D612E32596E39B4F670DD34D12D5494713A6AA075239EAEE302B'
$expectedCanonical = 'FE457F55F5C98ECA5A5E6380F2601FA5B949DA8037932599BB98018EC4E16753'
$expectedStored = '8AD18B21D993B476CC6DEE8FEEDE486F6FA8D712A650A0674AC458A538D23B65'
$expectedSource = 'fc954c42a5385c0c705b1d8ace4df66d82a46e0b'
$expectedMathlib = '07642720480157414db592fa85b626dafb71355b'
$expectedToolchain = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
$expectedRunner = 'cmp89-neumann-recursive-poincare-coefficient-cold-v1'
$expectedStages = @(
  'download_toolchain', 'apt_update', 'install_zstd', 'extract_toolchain',
  'lean_version', 'lake_version', 'clone', 'checkout', 'head',
  'overlay_text_guard', 'import_prefix_guard', 'lake_update', 'mathlib_pin',
  'cache_get', 'recursive_poincare_coefficient_focal',
  'recursive_poincare_coefficient_audit'
)
$expectedBlobs = @{
  'YangMills/RG/BalabanCMP89SourceNeumannRecursivePoincareCoefficient.lean' =
    'b75df20fc81cf2fbc89bdc7823d7c259d90f5a8d38c0c6891f8765c2276cae95'
  'YangMills/RG/BalabanCMP89SourceNeumannRecursivePoincareCoefficientAudit.lean' =
    '1bd4c326fc2c9262220bf0ee5f4a55f107a61aff7d6d921f0077e0168b567fbc'
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

Write-Output 'CMP89_NEUMANN_RECURSIVE_POINCARE_COEFFICIENT_COLD_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$archiveHash"
Write-Output "CANONICAL_EVIDENCE_SHA256=$canonicalHash"
Write-Output "STORED_EVIDENCE_JSON_SHA256=$storedHash"
Write-Output "RECORD_COUNT=$(@($payload.records).Count)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
