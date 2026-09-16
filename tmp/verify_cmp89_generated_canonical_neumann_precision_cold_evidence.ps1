param(
  [Parameter(Mandatory = $true)][string]$Archive,
  [Parameter(Mandatory = $true)][string]$Destination
)

$ErrorActionPreference = 'Stop'
$expectedArchive = 'C525FF4EF5E4992834D4AC21832DE5BBF5143E9A660C9D425E182A9109AAC4ED'
$expectedCanonical = 'A7A29323DC3BE0810724CA47EECA2C6FD8A49DC45EDA8E131AC7E5CF3D8FF48C'
$expectedStored = '5B9DE912FADD30F903A927BB028125DCC5A78C741F6422E9EBE9B9820205871B'
$expectedSource = 'bf678d9d25c504bc2d012794634b8941b62fef8e'
$expectedMathlib = '07642720480157414db592fa85b626dafb71355b'
$expectedToolchain = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
$expectedRunner = 'cmp89-generated-canonical-neumann-precision-cold-v1'
$expectedStages = @(
  'download_toolchain', 'apt_update', 'install_zstd', 'extract_toolchain',
  'lean_version', 'lake_version', 'clone', 'checkout', 'head',
  'overlay_text_guard', 'import_prefix_guard', 'lake_update', 'mathlib_pin',
  'cache_get', 'generated_canonical_neumann_precision_focal',
  'generated_canonical_neumann_precision_audit'
)
$expectedBlobs = @{
  'YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecision.lean' =
    'bc0a9892947bcf193c688a127d3c21cd29bcc0b2ed76507ed5bed53d50f09172'
  'YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannPrecisionAudit.lean' =
    '34fed8e50154d5726ab477026f233c34cbc3bdb40d9c652761a7e9dcfe360321'
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

Write-Output 'CMP89_GENERATED_CANONICAL_NEUMANN_PRECISION_COLD_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$archiveHash"
Write-Output "CANONICAL_EVIDENCE_SHA256=$canonicalHash"
Write-Output "STORED_EVIDENCE_JSON_SHA256=$storedHash"
Write-Output "RECORD_COUNT=$(@($payload.records).Count)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
