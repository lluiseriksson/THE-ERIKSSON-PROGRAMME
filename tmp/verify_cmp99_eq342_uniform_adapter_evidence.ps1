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
if ($payload.source_sha -ne 'd8db241ce99ef37ceecc14afefc3a19b88ed5f20') {
  throw "SOURCE_SHA_MISMATCH=$($payload.source_sha)"
}
if ($payload.restored_project_build -ne $false) { throw 'PROJECT_BUILD_WAS_RESTORED' }

foreach ($stage in @('eq342_uniform_adapter_focal', 'eq342_uniform_adapter_audit')) {
  $record = @($payload.records | Where-Object { $_.stage -eq $stage })
  if ($record.Count -ne 1 -or $record[0].exit -ne 0) {
    throw "STAGE_RECORD_INVALID=$stage"
  }
  if ($stage.EndsWith('_focal') -and -not $record[0].jobs) {
    throw "FOCAL_JOBS_MISSING=$stage"
  }
}

$audit = Get-ChildItem -LiteralPath $Destination -Recurse -File |
  Where-Object {
    $_.Name -match 'eq342_uniform_adapter_audit' -and $_.Extension -eq '.stdout'
  } | Select-Object -First 1
if (-not $audit) { throw 'AUDIT_LOG_MISSING=eq342_uniform_adapter_audit' }
$auditText = Get-Content -Raw -LiteralPath $audit.FullName
foreach ($forbidden in @('sorryAx', 'ofReduceBool')) {
  if ($auditText.Contains($forbidden)) { throw "FORBIDDEN_AXIOM=$forbidden" }
}
$compact = $auditText -replace '\s+', ''
$seen = @(
  [regex]::Matches($compact, "'([^']+)'dependsonaxioms:\[") |
    ForEach-Object { $_.Groups[1].Value }
)
$declaration = 'YangMills.RG.cmp99Eq342SourceLocalizedGreenCertificate_of_uniformValueBound'
if ($seen.Count -ne 1 -or $seen[0] -ne $declaration) {
  throw "AXIOM_DECLARATION_MISMATCH=$($seen -join ',')"
}

Write-Output 'CMP99_EQ342_UNIFORM_ADAPTER_EVIDENCE_OK'
Write-Output "ARCHIVE_SHA256=$measured"
Write-Output "MANIFEST_ENTRIES=$count"
Write-Output "FOCAL_JOBS=$((@($payload.records | Where-Object stage -eq 'eq342_uniform_adapter_focal'))[0].jobs)"
Write-Output "EVIDENCE_JSON=$($evidence.FullName)"
