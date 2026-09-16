param(
  [Parameter(Mandatory = $true)][string]$Archive,
  [Parameter(Mandatory = $true)][string]$Destination
)

$ErrorActionPreference = 'Stop'
$expectedArchive = '35517565DB479A332FDDDC295D38939641205B0C92C70E668B3856AD1817B7C6'
$expectedCanonical = 'E8A95941A7A8A78FA377D728F0DD19329E378CBFBB330F1F98C1E36424B17C92'
$expectedStored = 'B97C733B0AE9FC248B4152DBFC47DD01420DFE73864F66D6AE13CC35FA2BCB88'
$expectedSource = 'cdd859ba99671e83a1ef2b3d8119a4e376a97ced'
$expectedMathlib = '07642720480157414db592fa85b626dafb71355b'
$expectedToolchain = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
$expectedRunner = 'cmp89-neumann-reflection-inverse-cold-v1'
$expectedStages = @(
  'download_toolchain', 'apt_update', 'install_zstd', 'extract_toolchain',
  'lean_version', 'lake_version', 'clone', 'checkout', 'head',
  'overlay_text_guard', 'import_prefix_guard', 'lake_update', 'mathlib_pin',
  'cache_get', 'neumann_rectangle_specialization_focal',
  'neumann_rectangle_specialization_audit',
  'neumann_rectangle_physical_specialization_focal',
  'neumann_rectangle_physical_specialization_audit',
  'neumann_scalar_reflection_operator_focal',
  'neumann_scalar_reflection_operator_audit',
  'neumann_reflection_inverse_producer_focal',
  'neumann_reflection_inverse_producer_audit',
  'neumann_physical_real_summability_focal',
  'neumann_physical_real_summability_audit'
)
$expectedBlobs = @{
  'YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentation.lean' = 'f3cc06c780ac08dab545646303cc24abb4a4f3b6d611eb090f8975333178bb7f'
  'YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectangleReflectionRepresentationAudit.lean' = 'ab96c9e06c46bfcb98bfc9b55d73bcb3dac6f2956ebc04b8058da0371cf3583b'
  'YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentation.lean' = '773c1940c132dc0f298061a9a91b79061724907a341809e5ae8f5774aa14f9ae'
  'YangMills/RG/BalabanCMP89SourceFlatGeneratedFiniteDepthCanonicalNeumannRectanglePhysicalReflectionRepresentationAudit.lean' = '9c28fc57c3c33c3acdbf968f7b64b03a2dff102a46050e6baa7713356a888422'
  'YangMills/RG/BalabanCMP89NeumannScalarReflectionOperator.lean' = '699ca04c04c31900aa23a750d417bf3b716411df785794a6701aa3321d68f70e'
  'YangMills/RG/BalabanCMP89NeumannScalarReflectionOperatorAudit.lean' = 'a0a0fbebbefa2833c9435afd822ea76d35e331f30a45762b2469cbde4d085d73'
  'YangMills/RG/BalabanCMP89CanonicalNeumannReflectionInverseProducer.lean' = '62bcfd6336e1a8582393acc38f0fb9153a9c54bfc5d59c291b523a1f52e1d9d7'
  'YangMills/RG/BalabanCMP89CanonicalNeumannReflectionInverseProducerAudit.lean' = '44882d0ec10fe5cfa6fa156acb2a5551e8156cbdd46a3c94c951a5984e03fdfe'
  'YangMills/RG/BalabanCMP89NeumannPhysicalRealReflectionSummability.lean' = 'd5b982f8f5715a42f56f9f3b57df334deb33c37dd6aed048840e5c18137d8312'
  'YangMills/RG/BalabanCMP89NeumannPhysicalRealReflectionSummabilityAudit.lean' = 'c950ba2f4ca36bc88c8d8ef8846a2cf600af7040cbe65d88191753ae01584a12'
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

Write-Output 'CMP89_NEUMANN_REFLECTION_INVERSE_COLD_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$archiveHash"
Write-Output "CANONICAL_EVIDENCE_SHA256=$canonicalHash"
Write-Output "STORED_EVIDENCE_JSON_SHA256=$storedHash"
Write-Output "RECORD_COUNT=$(@($payload.records).Count)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
