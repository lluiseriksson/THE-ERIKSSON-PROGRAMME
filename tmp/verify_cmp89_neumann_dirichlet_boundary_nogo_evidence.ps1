param(
  [Parameter(Mandatory = $true)][string]$Archive,
  [Parameter(Mandatory = $true)][string]$ExpectedSha256,
  [Parameter(Mandatory = $true)][string]$ExpectedEvidenceSha256,
  [Parameter(Mandatory = $true)][string]$Notebook,
  [Parameter(Mandatory = $true)][string]$Destination
)

$ErrorActionPreference = 'Stop'

$expectedSource = '1721fb8b8655e4e6f9bb15fc0e0440750ff013d9'
$expectedMathlib = '07642720480157414db592fa85b626dafb71355b'
$expectedToolchain = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
$expectedRunnerRev = 'cmp89-neumann-dirichlet-boundary-nogo-v1'
$expectedRunnerTransport = 'bc560edef280f23c754a5140570cf0c7bf94664b28ee521711a471bfabc9998a'
$expectedRunnerCommit = '8e3e8a6fef9a812546e6550fa432507697fe78a6'
$expectedStages = @(
  'cmp89_source_neumann_precision_focal',
  'cmp89_source_neumann_precision_audit',
  'cmp89_neumann_dirichlet_boundary_nogo_focal',
  'cmp89_neumann_dirichlet_boundary_nogo_audit',
  'cmp89_neumann_dirichlet_boundary_nogo_root'
)
$expectedStageOutputs = @{
  'cmp89_source_neumann_precision_focal' = '16cf94f2b54c59914a72238ec8dcadc33e94485f80532a51b9b829a803bc0b35'
  'cmp89_source_neumann_precision_audit' = '208f465ddb18340042eb387e120197878bb4f243e6c06cb85a87d3c5b21ea5f2'
  'cmp89_neumann_dirichlet_boundary_nogo_focal' = 'da4a30122467afa96958920153e6cb371b02fe9ede8ef525e408dfef74edd069'
  'cmp89_neumann_dirichlet_boundary_nogo_audit' = 'c07cad2ba7a5848eb85b0ecf566ed59c88b6b6a4fad86394c9d49a2ca9c804ee'
  'cmp89_neumann_dirichlet_boundary_nogo_root' = '7bf4b723ddfe4c75c15e808f90b00bb966a671aedab16c0394792f8c833a002e'
}
$expectedDeclarations = @(
  'YangMills.RG.inner_cmp89SourceNeumannRegionalLaplacian',
  'YangMills.RG.cmp89SourceNeumannRegionalLaplacian_isSymmetric',
  'YangMills.RG.cmp89SourceNeumannRegionalCovariantD0CLM_boundary_eq_zero',
  'YangMills.RG.cmp99ActiveRegionSourceCovariantD0CLM_boundary_eq',
  'YangMills.RG.cmp89SourceNeumannRegionalCovariantD0CLM_ne_dirichlet_of_boundary'
)
$expectedBlobs = @{
  'YangMills/RG/BalabanCMP89SourceNeumannRegionalPrecision.lean' = '6b7bd0dca8e66012fd29f88ee127ba03d79872b539abcb202ebb38332cb15e68'
  'YangMills/RG/BalabanCMP89SourceNeumannRegionalPrecisionAudit.lean' = 'eb8cb9d56a7f1dd3bdff5b423a5deb8effa4bb98b524963e8dcf9e3d80cd9838'
  'YangMills/RG/BalabanCMP89NeumannDirichletBoundaryNoGo.lean' = 'b499f7aba1d39a66ca95efb78cb6277702aff4b72e435e58c9e20d761449b6f1'
  'YangMills/RG/BalabanCMP89NeumannDirichletBoundaryNoGoAudit.lean' = 'd3465d86f9eea7c76655df7575e5daecb2633b3e877d1e9851dcb7bd2b14ca8b'
  'YangMillsCore.lean' = '9a9b20f2ed0100ca668bfb1534fa22c00aef03dfdc8958e497667526b8bbc8ea'
}
$allowedAxioms = @('propext', 'Classical.choice', 'Quot.sound')

$measured = (Get-FileHash -Algorithm SHA256 -LiteralPath $Archive).Hash
if ($measured -ne $ExpectedSha256.ToUpperInvariant()) {
  throw "ARCHIVE_HASH_MISMATCH expected=$ExpectedSha256 measured=$measured"
}
if (Test-Path -LiteralPath $Destination) {
  throw "DESTINATION_ALREADY_EXISTS=$Destination"
}

$members = @(tar -tzf $Archive)
if ($LASTEXITCODE -ne 0) { throw "ARCHIVE_LIST_FAILED exit=$LASTEXITCODE" }
$files = @($members | Where-Object { $_ -and -not $_.EndsWith('/') })
if ($files.Count -ne 1 -or -not $files[0].EndsWith('/evidence.json')) {
  throw "ARCHIVE_MEMBERS_INVALID=$($members -join ',')"
}

New-Item -ItemType Directory -Path $Destination | Out-Null
tar -xzf $Archive -C $Destination
if ($LASTEXITCODE -ne 0) { throw "ARCHIVE_EXTRACT_FAILED exit=$LASTEXITCODE" }

$evidence = Get-ChildItem -LiteralPath $Destination -Recurse -File -Filter 'evidence.json' | Select-Object -First 1
if (-not $evidence) { throw 'EVIDENCE_JSON_MISSING' }
$evidenceRaw = Get-Content -Raw -LiteralPath $evidence.FullName
$evidencePayload = $evidenceRaw.TrimEnd("`r", "`n")
$sha = [System.Security.Cryptography.SHA256]::Create()
try {
  $digest = $sha.ComputeHash([System.Text.Encoding]::UTF8.GetBytes($evidencePayload))
  $evidenceHash = ([System.BitConverter]::ToString($digest)).Replace('-', '')
} finally {
  $sha.Dispose()
}
if ($evidenceHash -ne $ExpectedEvidenceSha256.ToUpperInvariant()) {
  throw "EVIDENCE_JSON_HASH_MISMATCH expected=$ExpectedEvidenceSha256 measured=$evidenceHash"
}
$payload = $evidenceRaw | ConvertFrom-Json
if ($payload.status -ne 'PASS') { throw "EVIDENCE_STATUS_NOT_PASS=$($payload.status)" }
if ($payload.source_sha -ne $expectedSource) { throw "SOURCE_SHA_MISMATCH=$($payload.source_sha)" }
if ($payload.mathlib_sha -ne $expectedMathlib) { throw "MATHLIB_SHA_MISMATCH=$($payload.mathlib_sha)" }
if ($payload.toolchain_asset_sha256 -ne $expectedToolchain) { throw "TOOLCHAIN_SHA_MISMATCH=$($payload.toolchain_asset_sha256)" }
if ($payload.runner_rev -ne $expectedRunnerRev) { throw "RUNNER_REV_MISMATCH=$($payload.runner_rev)" }

$blobNames = @($payload.source_blobs.PSObject.Properties.Name)
if ($blobNames.Count -ne $expectedBlobs.Count) { throw "SOURCE_BLOB_COUNT=$($blobNames.Count)" }
foreach ($path in $expectedBlobs.Keys) {
  $actual = $payload.source_blobs.PSObject.Properties[$path].Value
  if ($actual -ne $expectedBlobs[$path]) { throw "SOURCE_BLOB_MISMATCH=$path" }
}

foreach ($stage in $expectedStages) {
  $record = @($payload.records | Where-Object { $_.stage -eq $stage })
  if ($record.Count -ne 1 -or $record[0].exit -ne 0) { throw "STAGE_RECORD_INVALID=$stage" }
  if ($record[0].output_sha256 -ne $expectedStageOutputs[$stage]) {
    throw "STAGE_OUTPUT_HASH_MISMATCH=$stage"
  }
}

$nb = Get-Content -Raw -LiteralPath $Notebook | ConvertFrom-Json
$matchingCells = @($nb.cells | Where-Object { (($_.source -join '') -match [regex]::Escape($expectedRunnerTransport)) })
if ($matchingCells.Count -ne 1) { throw "RUNNER_CELL_COUNT=$($matchingCells.Count)" }
$cell = $matchingCells[0]
$cellSource = $cell.source -join ''
if (-not $cellSource.Contains($expectedRunnerCommit)) { throw "RUNNER_COMMIT_MISSING=$expectedRunnerCommit" }
if ($cell.execution_count -ne 1) { throw "RUNNER_CELL_EXECUTION_COUNT=$($cell.execution_count)" }
$pieces = New-Object System.Collections.Generic.List[string]
foreach ($output in @($cell.outputs)) {
  if ($null -ne $output.text) { $pieces.Add(($output.text -join '')) }
  if ($null -ne $output.data -and $null -ne $output.data.'text/plain') { $pieces.Add(($output.data.'text/plain' -join '')) }
}
$transcript = $pieces -join "`n"
foreach ($required in @(
  'Build completed successfully (11185 jobs).',
  "EVIDENCE_SHA256=$($ExpectedEvidenceSha256.ToLowerInvariant())",
  "EVIDENCE_ARCHIVE_SHA256=$($ExpectedSha256.ToLowerInvariant())",
  'FINAL_STATUS=PASS',
  'LAUNCHER_EXIT=0'
)) {
  if (-not $transcript.Contains($required)) { throw "TRANSCRIPT_TOKEN_MISSING=$required" }
}
if ($transcript -notmatch 'STAGE=cmp89_neumann_dirichlet_boundary_nogo_root EXIT=0 SECONDS=[0-9.]+') {
  throw 'TRANSCRIPT_ROOT_STAGE_MISSING'
}
foreach ($forbidden in @('sorryAx', 'ofReduceBool')) {
  if ($transcript.Contains($forbidden)) { throw "FORBIDDEN_AXIOM=$forbidden" }
}

$notebookHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $Notebook).Hash
Copy-Item -LiteralPath $Archive -Destination (Join-Path $Destination 'evidence.tar.gz')
Copy-Item -LiteralPath $Notebook -Destination (Join-Path $Destination 'executed-colab.ipynb')
Write-Output 'CMP89_NEUMANN_DIRICHLET_BOUNDARY_NOGO_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$measured"
Write-Output "EVIDENCE_JSON_SHA256=$evidenceHash"
Write-Output "NOTEBOOK_SHA256=$notebookHash"
foreach ($stage in $expectedStages) {
  $record = @($payload.records | Where-Object { $_.stage -eq $stage })[0]
  Write-Output "STAGE=$stage EXIT=$($record.exit) SECONDS=$($record.seconds) OUTPUT_SHA256=$($record.output_sha256)"
}
Write-Output 'ROOT_JOBS=11185'
Write-Output "AXIOM_GATES=$($expectedDeclarations.Count)"
Write-Output 'AXIOM_EVIDENCE=PINNED_AUDIT_OUTPUT_HASHES'
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
