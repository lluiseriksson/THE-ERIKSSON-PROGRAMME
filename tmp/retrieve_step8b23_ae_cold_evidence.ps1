[CmdletBinding()]
param(
  [Parameter(Mandatory = $true)][long]$RunId,
  [Parameter(Mandatory = $true)]
  [ValidatePattern('^[0-9a-f]{40}$')][string]$SourceSha,
  [Parameter(Mandatory = $true)]
  [ValidatePattern('^[0-9a-f]{40}$')][string]$WorkflowSha,
  [Parameter(Mandatory = $true)][string]$Destination
)

$ErrorActionPreference = 'Stop'
$repo = Split-Path -Parent $PSScriptRoot
if (-not (Test-Path -LiteralPath (Join-Path $repo '.git'))) {
  throw "Repository root not found from $PSScriptRoot"
}

$destinationPath = [IO.Path]::GetFullPath($Destination)
if (Test-Path -LiteralPath $destinationPath) {
  throw "Destination already exists: $destinationPath"
}

$auth = gh auth status --hostname github.com 2>&1 | Out-String
if ($LASTEXITCODE -ne 0) { throw "gh auth status failed: $auth" }
if ($auth -notmatch 'account lluiseriksson') {
  throw "Wrong GitHub account; expected lluiseriksson"
}

$runJson = gh run view $RunId `
  --repo lluiseriksson/THE-ERIKSSON-PROGRAMME `
  --json status,conclusion,headSha,url
if ($LASTEXITCODE -ne 0) { throw "Cannot read run $RunId" }
$run = $runJson | ConvertFrom-Json
if ($run.status -ne 'completed') { throw "Run is not completed: $($run.status)" }
if ($run.conclusion -ne 'success') { throw "Run did not succeed: $($run.conclusion)" }
if ($run.headSha -ne $WorkflowSha) {
  throw "Workflow SHA mismatch: $($run.headSha)"
}

$artifactName = "step8b23-ae-$SourceSha"
$artifactJson = gh api `
  "repos/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/runs/$RunId/artifacts"
if ($LASTEXITCODE -ne 0) { throw "Cannot list artifacts for run $RunId" }
$artifactResponse = $artifactJson | ConvertFrom-Json
$artifactIds = @(
  $artifactResponse.artifacts |
    Where-Object { $_.name -eq $artifactName } |
    ForEach-Object { $_.id }
)
if ($artifactIds.Count -ne 1) {
  throw "Expected exactly one $artifactName artifact; found $($artifactIds.Count)"
}

New-Item -ItemType Directory -Path $destinationPath | Out-Null
$rawZip = Join-Path $destinationPath 'step8b23-ae-github-artifact.zip'
$extracted = Join-Path $destinationPath 'extracted'
New-Item -ItemType Directory -Path $extracted | Out-Null

# PowerShell 5 text redirection corrupts binary responses.  gh uses the
# authenticated keyring; no token is exposed on the command line.
$artifactId = $artifactIds[0]
$cmd = 'gh api repos/lluiseriksson/THE-ERIKSSON-PROGRAMME/actions/artifacts/' +
  $artifactId + '/zip > "' + $rawZip.Replace('"', '""') + '"'
cmd.exe /d /c $cmd
if ($LASTEXITCODE -ne 0) { throw "Raw artifact ZIP download failed" }
if (-not (Test-Path -LiteralPath $rawZip -PathType Leaf)) {
  throw "Raw artifact ZIP missing after download"
}

gh run download $RunId `
  --repo lluiseriksson/THE-ERIKSSON-PROGRAMME `
  --name $artifactName `
  --dir $extracted
if ($LASTEXITCODE -ne 0) { throw "Artifact extraction download failed" }

python (Join-Path $repo 'tmp\audit_step8b23_ae_cold_evidence.py') `
  --artifact-root $extracted `
  --outer-zip $rawZip `
  --source-sha $SourceSha `
  --workflow-sha $WorkflowSha
if ($LASTEXITCODE -ne 0) { throw "Independent cold-evidence audit failed" }

$zipSha = (Get-FileHash -LiteralPath $rawZip -Algorithm SHA256).Hash
Write-Output "STEP8B23_AE_RETRIEVAL_OK"
Write-Output "run_id=$RunId"
Write-Output "run_url=$($run.url)"
Write-Output "source_sha=$SourceSha"
Write-Output "workflow_sha=$WorkflowSha"
Write-Output "artifact_name=$artifactName"
Write-Output "artifact_id=$artifactId"
Write-Output "raw_outer_zip_sha256=$zipSha"
Write-Output "destination=$destinationPath"
