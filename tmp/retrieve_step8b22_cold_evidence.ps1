param(
  [string]$Repo = 'lluiseriksson/THE-ERIKSSON-PROGRAMME',
  [string]$Destination = 'validation-evidence/run-31991954503'
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$RunId = '31991954503'
$ArtifactName = 'cmp99-finite-grid-aliasing-534493728038813f3772f8b3b073237f4da1884e'
$ExpectedSource = '534493728038813f3772f8b3b073237f4da1884e'
$ExpectedWorkflow = 'b05ef65af97a95752d1c929e30749d886d425d8d'

if (Test-Path -LiteralPath $Destination) {
  throw "Refusing to overwrite existing evidence destination: $Destination"
}

$auth = gh auth status --hostname github.com 2>&1
$authExit = $LASTEXITCODE
$authText = $auth -join "`n"
if ($authExit -ne 0 -or ($authText -notmatch 'Logged in to github.com account lluiseriksson')) {
  throw "GitHub authentication gate failed: $authText"
}

$artifactJson = gh api "repos/$Repo/actions/runs/$RunId/artifacts"
if ($LASTEXITCODE -ne 0) {
  throw 'Artifact-list API call failed'
}
$artifactResponse = ConvertFrom-Json ($artifactJson -join "`n")
$ids = @(
  $artifactResponse.artifacts |
    Where-Object { $_.name -eq $ArtifactName } |
    ForEach-Object { [string]$_.id }
)
if ($ids.Count -ne 1) {
  throw "Expected exactly one artifact named $ArtifactName; found $($ids.Count)"
}

New-Item -ItemType Directory -Path $Destination | Out-Null
$destinationFull = (Resolve-Path -LiteralPath $Destination).Path
$rawZip = Join-Path $destinationFull 'step8b22-github-artifact.zip'
$extracted = Join-Path $destinationFull 'extracted'
$artifactIdValue = $ids[0]

# PowerShell 5.1 text redirection can corrupt a ZIP.  Keep binary redirection
# inside cmd.exe; gh reads its credential from the authenticated keyring.
$apiPath = "repos/$Repo/actions/artifacts/$artifactIdValue/zip"
$cmdLine = "gh api $apiPath > `"$rawZip`""
& cmd.exe /d /s /c $cmdLine
if ($LASTEXITCODE -ne 0 -or -not (Test-Path -LiteralPath $rawZip)) {
  throw 'Raw artifact ZIP download failed'
}

gh run download $RunId --repo $Repo --name $ArtifactName --dir $extracted
if ($LASTEXITCODE -ne 0) {
  throw 'Artifact extraction download failed'
}

python tmp/audit_step8b22_cold_evidence.py `
  --artifact-root $extracted --outer-zip $rawZip
if ($LASTEXITCODE -ne 0) {
  throw 'STEP8B22 cold-evidence validator rejected the artifact'
}

$outerHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $rawZip).Hash
Write-Output "STEP8B22_EVIDENCE_RETRIEVAL_OK"
Write-Output "RUN_ID=$RunId"
Write-Output "ARTIFACT_ID=$artifactIdValue"
Write-Output "ARTIFACT_NAME=$ArtifactName"
Write-Output "EXPECTED_SOURCE=$ExpectedSource"
Write-Output "EXPECTED_WORKFLOW=$ExpectedWorkflow"
Write-Output "OUTER_ZIP_SHA256=$outerHash"
Write-Output "DESTINATION=$destinationFull"
