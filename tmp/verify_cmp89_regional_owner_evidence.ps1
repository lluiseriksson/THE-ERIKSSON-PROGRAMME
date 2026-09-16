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
if ($LASTEXITCODE -ne 0) {
  throw "ARCHIVE_EXTRACT_FAILED exit=$LASTEXITCODE"
}

$manifest = Get-ChildItem -LiteralPath $Destination -Recurse -File -Filter 'MANIFEST.sha256' |
  Select-Object -First 1
if (-not $manifest) {
  throw 'MANIFEST_MISSING'
}

$root = $manifest.Directory.FullName
$entries = Get-Content -LiteralPath $manifest.FullName
$count = 0
foreach ($entry in $entries) {
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
  if ($actual -ne $expected) {
    throw "MANIFEST_MEMBER_HASH_MISMATCH=$relative"
  }
  $count++
}

$evidence = Get-ChildItem -LiteralPath $Destination -Recurse -File -Filter 'evidence.json' |
  Select-Object -First 1
if (-not $evidence) {
  throw 'EVIDENCE_JSON_MISSING'
}
$payload = Get-Content -Raw -LiteralPath $evidence.FullName | ConvertFrom-Json
if ($payload.status -ne 'PASS') {
  throw "EVIDENCE_STATUS_NOT_PASS=$($payload.status)"
}
if ($payload.source_sha -ne 'b9561132d1eaa2e55d4638bf42f1632effd64d68') {
  throw "SOURCE_SHA_MISMATCH=$($payload.source_sha)"
}
if ($payload.restored_project_build -ne $false) {
  throw 'PROJECT_BUILD_WAS_RESTORED'
}
$focalRecord = @($payload.records | Where-Object { $_.stage -eq 'focal' })
$auditRecord = @($payload.records | Where-Object { $_.stage -eq 'audit' })
if ($focalRecord.Count -ne 1 -or $focalRecord[0].exit -ne 0 -or
    -not $focalRecord[0].jobs) {
  throw 'FOCAL_RECORD_INVALID'
}
if ($auditRecord.Count -ne 1 -or $auditRecord[0].exit -ne 0) {
  throw 'AUDIT_RECORD_INVALID'
}

$audit = Get-ChildItem -LiteralPath $Destination -Recurse -File |
  Where-Object { $_.Name -match 'audit' -and $_.Extension -eq '.stdout' } |
  Select-Object -First 1
if (-not $audit) {
  throw 'AUDIT_LOG_MISSING'
}
$auditText = Get-Content -Raw -LiteralPath $audit.FullName
foreach ($forbidden in @('sorryAx', 'ofReduceBool')) {
  if ($auditText.Contains($forbidden)) {
    throw "FORBIDDEN_AXIOM=$forbidden"
  }
}
$compactAudit = $auditText -replace '\s+', ''
$expectedDeclarations = @(
  'YangMills.RG.cmp89NeumannReflectionPeriodProduct_uniform_le_draft',
  'YangMills.RG.cmp89NeumannFineWeight_le_ownerWeight_of_metric_bridge_draft',
  'YangMills.RG.norm_cmp89Eq248PhysicalRegionalGreen_le_owner_of_geometry_draft'
)
$seenDeclarations = @(
  [regex]::Matches($compactAudit, "'([^']+)'dependsonaxioms:\[") |
    ForEach-Object { $_.Groups[1].Value }
)
if ($seenDeclarations.Count -ne $expectedDeclarations.Count) {
  throw "AXIOM_DECLARATION_COUNT_MISMATCH=$($seenDeclarations.Count)"
}
foreach ($declaration in $expectedDeclarations) {
  if ($declaration -notin $seenDeclarations) {
    throw "AXIOM_DECLARATION_MISSING=$declaration"
  }
}

Write-Output 'CMP89_REGIONAL_OWNER_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$measured"
Write-Output "MANIFEST_ENTRIES=$count"
Write-Output "FOCAL_JOBS=$($focalRecord[0].jobs)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
