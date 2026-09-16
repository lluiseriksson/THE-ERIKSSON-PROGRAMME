param(
  [string]$Repo = 'lluiseriksson/THE-ERIKSSON-PROGRAMME',
  [string]$Branch = 'codex/cmp116-interacting-wilson-hessian',
  [string]$DestinationRoot = ''
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$ExpectedControl = 'ebccd7e8811d639587563fe060705811163e1c57'
$ExpectedSource = '73bb1a2008c557840a91e50d8abe6b874947f7ee'
$Workflow = 'validate-localized-carrier.yml'
$ArtifactName = "source-flow-uniform-localized-b0-$ExpectedSource"
$scriptRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
if ([string]::IsNullOrWhiteSpace($DestinationRoot)) {
  $DestinationRoot = Join-Path (Split-Path -Parent $scriptRoot) 'validation-evidence'
}

$auth = gh auth status --hostname github.com 2>&1
$authExit = $LASTEXITCODE
$authText = $auth -join "`n"
if ($authExit -ne 0 -or ($authText -notmatch 'Logged in to github.com account lluiseriksson')) {
  throw "GitHub authentication gate failed: $authText"
}

$runsJson = gh run list --repo $Repo --workflow $Workflow --branch $Branch --limit 100 `
  --json databaseId,headSha,status,conclusion,url
if ($LASTEXITCODE -ne 0) {
  throw 'Run-list API call failed'
}
$runs = @(ConvertFrom-Json ($runsJson -join "`n") | Where-Object { $_.headSha -eq $ExpectedControl })
if ($runs.Count -ne 1) {
  throw "Expected exactly one workflow run at control SHA $ExpectedControl; found $($runs.Count)"
}
$run = $runs[0]
if ($run.status -ne 'completed') {
  throw "Terminal run is not completed: status=$($run.status) url=$($run.url)"
}
$RunId = [string]$run.databaseId
$Destination = Join-Path $DestinationRoot "uniform-localized-b0-run-$RunId"
if (Test-Path -LiteralPath $Destination) {
  throw "Refusing to overwrite existing evidence destination: $Destination"
}

$artifactJson = gh api "repos/$Repo/actions/runs/$RunId/artifacts"
if ($LASTEXITCODE -ne 0) {
  throw 'Artifact-list API call failed'
}
$response = ConvertFrom-Json ($artifactJson -join "`n")
$ids = @($response.artifacts | Where-Object { $_.name -eq $ArtifactName } |
  ForEach-Object { [string]$_.id })
if ($ids.Count -ne 1) {
  throw "Expected exactly one artifact named $ArtifactName; found $($ids.Count)"
}

New-Item -ItemType Directory -Path $Destination | Out-Null
$destinationFull = (Resolve-Path -LiteralPath $Destination).Path
$rawZip = Join-Path $destinationFull 'github-artifact.zip'
$extracted = Join-Path $destinationFull 'extracted'
$artifactId = $ids[0]
$apiPath = "repos/$Repo/actions/artifacts/$artifactId/zip"
$cmdLine = "gh api $apiPath > `"$rawZip`""
& cmd.exe /d /s /c $cmdLine
if ($LASTEXITCODE -ne 0 -or -not (Test-Path -LiteralPath $rawZip)) {
  throw 'Raw artifact ZIP download failed'
}

gh run download $RunId --repo $Repo --name $ArtifactName --dir $extracted
if ($LASTEXITCODE -ne 0) {
  throw 'Artifact extraction download failed'
}

python (Join-Path $scriptRoot 'audit_uniform_localized_b0_terminal_evidence.py') `
  --artifact-root $extracted --outer-zip $rawZip
if ($LASTEXITCODE -ne 0) {
  throw 'Uniform/localized B0 terminal evidence validator rejected the artifact'
}

$outerHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $rawZip).Hash
Write-Output 'UNIFORM_LOCALIZED_B0_EVIDENCE_RETRIEVAL_OK'
Write-Output "RUN_ID=$RunId"
Write-Output "RUN_CONCLUSION=$($run.conclusion)"
Write-Output "RUN_URL=$($run.url)"
Write-Output "ARTIFACT_ID=$artifactId"
Write-Output "ARTIFACT_NAME=$ArtifactName"
Write-Output "EXPECTED_SOURCE=$ExpectedSource"
Write-Output "EXPECTED_CONTROL=$ExpectedControl"
Write-Output "OUTER_ZIP_SHA256=$outerHash"
Write-Output "DESTINATION=$destinationFull"
