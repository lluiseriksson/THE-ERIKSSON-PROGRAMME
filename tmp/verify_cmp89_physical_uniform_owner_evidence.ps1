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
if ($payload.source_sha -ne '389d2626250f4b729253e74e6bc885166cb795fc') {
  throw "SOURCE_SHA_MISMATCH=$($payload.source_sha)"
}
if ($payload.restored_project_build -ne $false) { throw 'PROJECT_BUILD_WAS_RESTORED' }

foreach ($stage in @('physical_uniform_owner_focal', 'physical_uniform_owner_audit')) {
  $record = @($payload.records | Where-Object { $_.stage -eq $stage })
  if ($record.Count -ne 1 -or $record[0].exit -ne 0) {
    throw "STAGE_RECORD_INVALID=$stage"
  }
  if ($stage.EndsWith('_focal') -and -not $record[0].jobs) {
    throw "FOCAL_JOBS_MISSING=$stage"
  }
}

$audit = Get-ChildItem -LiteralPath $Destination -Recurse -File |
  Where-Object { $_.Name -match 'physical_uniform_owner_audit' -and $_.Extension -eq '.stdout' } |
  Select-Object -First 1
if (-not $audit) { throw 'AUDIT_LOG_MISSING=physical_uniform_owner_audit' }
$auditText = Get-Content -Raw -LiteralPath $audit.FullName
foreach ($forbidden in @('sorryAx', 'ofReduceBool')) {
  if ($auditText.Contains($forbidden)) { throw "FORBIDDEN_AXIOM=$forbidden" }
}
$compact = $auditText -replace '\s+', ''
$seen = @(
  [regex]::Matches($compact, "'([^']+)'dependsonaxioms:\[") |
    ForEach-Object { $_.Groups[1].Value }
)
$expectedDeclaration =
  'YangMills.RG.norm_cmp89Eq248PhysicalRegionalGreen_le_physicalOwner_uniform_draft'
if ($seen.Count -ne 1 -or $seen[0] -ne $expectedDeclaration) {
  throw "AXIOM_DECLARATION_MISMATCH=$($seen -join ',')"
}

Write-Output 'CMP89_PHYSICAL_UNIFORM_OWNER_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$measured"
Write-Output "MANIFEST_ENTRIES=$count"
Write-Output "FOCAL_JOBS=$((@($payload.records | Where-Object stage -eq 'physical_uniform_owner_focal'))[0].jobs)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
