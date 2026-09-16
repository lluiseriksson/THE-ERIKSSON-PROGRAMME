param(
  [string]$Repo = 'lluiseriksson/THE-ERIKSSON-PROGRAMME',
  [string]$Destination = 'validation-evidence/run-33470345841'
)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$RunId = '33470345841'
$ArtifactName = 'cmp89-eq246-full-solution-febce96d017f4ec8494354656f88b0dca56c1854'
$ExpectedHead = '6f1f0d646933fad80c4208868b9c926aa78f0d6f'

if (Test-Path -LiteralPath $Destination) {
  throw "Refusing to overwrite existing evidence destination: $Destination"
}

$auth = gh auth status --hostname github.com 2>&1
$authExit = $LASTEXITCODE
$authText = $auth -join "`n"
if ($authExit -ne 0 -or ($authText -notmatch 'Logged in to github.com account lluiseriksson')) {
  throw "GitHub authentication gate failed: $authText"
}

$runRaw = gh run view $RunId --repo $Repo --json status,conclusion,headSha
if ($LASTEXITCODE -ne 0) { throw 'Run-status query failed' }
$run = ConvertFrom-Json ($runRaw -join "`n")
if ($run.status -ne 'completed' -or $run.conclusion -ne 'success') {
  throw "RUN_NOT_SUCCESS status=$($run.status) conclusion=$($run.conclusion)"
}
if ($run.headSha -ne $ExpectedHead) {
  throw "RUN_HEAD_MISMATCH expected=$ExpectedHead actual=$($run.headSha)"
}

$artifactRaw = gh api "repos/$Repo/actions/runs/$RunId/artifacts"
if ($LASTEXITCODE -ne 0) { throw 'Artifact-list API call failed' }
$artifactResponse = ConvertFrom-Json ($artifactRaw -join "`n")
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
$rawZip = Join-Path $destinationFull 'github-artifact.zip'
$extracted = Join-Path $destinationFull 'extracted'
$artifactIdValue = $ids[0]

$apiPath = "repos/$Repo/actions/artifacts/$artifactIdValue/zip"
$cmdLine = "gh api $apiPath > `"$rawZip`""
& cmd.exe /d /s /c $cmdLine
if ($LASTEXITCODE -ne 0 -or -not (Test-Path -LiteralPath $rawZip)) {
  throw 'Raw artifact ZIP download failed'
}

gh run download $RunId --repo $Repo --name $ArtifactName --dir $extracted
if ($LASTEXITCODE -ne 0) { throw 'Artifact extraction download failed' }

python tmp/audit_cmp89_eq246_full_solution_cold_evidence.py `
  --artifact-root $extracted --outer-zip $rawZip
if ($LASTEXITCODE -ne 0) {
  throw 'CMP89 Eq246 cold-evidence validator rejected the artifact'
}

$outerHash = (Get-FileHash -Algorithm SHA256 -LiteralPath $rawZip).Hash
Write-Output 'CMP89_EQ246_FULL_SOLUTION_EVIDENCE_RETRIEVAL_OK'
Write-Output "RUN_ID=$RunId"
Write-Output "ARTIFACT_ID=$artifactIdValue"
Write-Output "ARTIFACT_NAME=$ArtifactName"
Write-Output "RUN_HEAD=$ExpectedHead"
Write-Output "OUTER_ZIP_SHA256=$outerHash"
Write-Output "DESTINATION=$destinationFull"
