param(
  [Parameter(Mandatory = $true)][string]$Archive,
  [Parameter(Mandatory = $true)][string]$ExpectedSha256,
  [Parameter(Mandatory = $true)][string]$Destination
)

$ErrorActionPreference = 'Stop'

$measured = (Get-FileHash -Algorithm SHA256 -LiteralPath $Archive).Hash
if ($measured -ne $ExpectedSha256.ToUpperInvariant()) {
  throw "ARCHIVE_HASH_MISMATCH expected=$ExpectedSha256 measured=$measured"
}
if (Test-Path -LiteralPath $Destination) {
  throw "DESTINATION_ALREADY_EXISTS=$Destination"
}

New-Item -ItemType Directory -Path $Destination | Out-Null
tar -xzf $Archive -C $Destination
if ($LASTEXITCODE -ne 0) { throw "ARCHIVE_EXTRACT_FAILED exit=$LASTEXITCODE" }

$manifest = Get-ChildItem -LiteralPath $Destination -Recurse -File -Filter 'MANIFEST.sha256' |
  Select-Object -First 1
if (-not $manifest) { throw 'MANIFEST_MISSING' }
$root = $manifest.Directory.FullName
$count = 0
foreach ($entry in Get-Content -LiteralPath $manifest.FullName) {
  if ($entry -notmatch '^([0-9a-fA-F]{64})  (.+)$') {
    throw "MANIFEST_LINE_INVALID=$entry"
  }
  $expected = $Matches[1].ToUpperInvariant()
  $relative = $Matches[2]
  $path = Join-Path $root $relative
  if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
    throw "MANIFEST_MEMBER_MISSING=$relative"
  }
  $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $path).Hash
  if ($actual -ne $expected) { throw "MANIFEST_MEMBER_HASH_MISMATCH=$relative" }
  $count++
}

$evidence = Get-ChildItem -LiteralPath $Destination -Recurse -File -Filter 'evidence.json' |
  Select-Object -First 1
if (-not $evidence) { throw 'EVIDENCE_JSON_MISSING' }
$payload = Get-Content -Raw -LiteralPath $evidence.FullName | ConvertFrom-Json
if ($payload.status -ne 'PASS') { throw "EVIDENCE_STATUS_NOT_PASS=$($payload.status)" }
if ($payload.source_sha -ne '1b9979c1371c68b6aaa9722afaa1314c41adfa49') {
  throw "SOURCE_SHA_MISMATCH=$($payload.source_sha)"
}
if ($payload.restored_project_build -ne $false) { throw 'PROJECT_BUILD_WAS_RESTORED' }

$stages = @(
  'period_floor_focal',
  'period_floor_audit',
  'physical_owner_geometry_focal',
  'physical_owner_geometry_audit'
)
foreach ($stage in $stages) {
  $record = @($payload.records | Where-Object { $_.stage -eq $stage })
  if ($record.Count -ne 1 -or $record[0].exit -ne 0) {
    throw "STAGE_RECORD_INVALID=$stage"
  }
  if ($stage.EndsWith('_focal') -and -not $record[0].jobs) {
    throw "FOCAL_JOBS_MISSING=$stage"
  }
}

$expectedByAudit = @{
  'period_floor_audit' = @(
    'YangMills.RG.cmp89NeumannReflectionPeriodNat_ge_scale_of_side_floor_draft'
  )
  'physical_owner_geometry_audit' = @(
    'YangMills.RG.cmp89SourceNeumannRectanglePointToFinBox_draft',
    'YangMills.RG.cmp89SourceNeumannRectanglePointToFinBox_val_draft',
    'YangMills.RG.finTorusDist_cmp89RectangleEmbedding_le_natAbs_sub_draft',
    'YangMills.RG.finBoxDist_cmp89RectangleEmbedding_le_l1_draft',
    'YangMills.RG.cmp89RectanglePhysicalOwner_mul_dist_le_l1_add_boundary_draft'
  )
}
foreach ($auditStage in $expectedByAudit.Keys) {
  $audit = Get-ChildItem -LiteralPath $Destination -Recurse -File |
    Where-Object { $_.Name -match $auditStage -and $_.Extension -eq '.stdout' } |
    Select-Object -First 1
  if (-not $audit) { throw "AUDIT_LOG_MISSING=$auditStage" }
  $text = Get-Content -Raw -LiteralPath $audit.FullName
  foreach ($forbidden in @('sorryAx', 'ofReduceBool')) {
    if ($text.Contains($forbidden)) { throw "FORBIDDEN_AXIOM=$forbidden" }
  }
  $compact = $text -replace '\s+', ''
  $seen = @(
    [regex]::Matches($compact, "'([^']+)'dependsonaxioms:\[") |
      ForEach-Object { $_.Groups[1].Value }
  )
  $expectedDeclarations = @($expectedByAudit[$auditStage])
  if ($seen.Count -ne $expectedDeclarations.Count) {
    throw "AXIOM_DECLARATION_COUNT_MISMATCH=$auditStage/$($seen.Count)"
  }
  foreach ($declaration in $expectedDeclarations) {
    if ($declaration -notin $seen) {
      throw "AXIOM_DECLARATION_MISSING=$declaration"
    }
  }
}

Write-Output 'CMP89_PHYSICAL_OWNER_GEOMETRY_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$measured"
Write-Output "MANIFEST_ENTRIES=$count"
Write-Output "PERIOD_JOBS=$((@($payload.records | Where-Object stage -eq 'period_floor_focal'))[0].jobs)"
Write-Output "GEOMETRY_JOBS=$((@($payload.records | Where-Object stage -eq 'physical_owner_geometry_focal'))[0].jobs)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
