$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$repo = 'C:\Users\lluis\Documents\Codex\2026-07-12\pu\work\THE-ERIKSSON-PROGRAMME-wilson-hessian'
$remote = 'github'
$branch = 'codex/cmp116-interacting-wilson-hessian'
$expectedParent = 'a754e28555270ebbdab8bff05f262368a39c43fa'
$expectedControl = 'ebccd7e8811d639587563fe060705811163e1c57'
$workflow = 'validate-localized-carrier.yml'
$expectedPath = '.github/workflows/validate-localized-carrier.yml'

Write-Host '== Publicación y CI terminal uniforme/localizada B0 =='
Write-Host 'Fail-closed: sin force-push, checkout, reset ni rerun.'

gh auth status --hostname github.com
$login = (gh api user --jq .login).Trim()
if ($LASTEXITCODE -ne 0 -or $login -ne 'lluiseriksson') {
  throw "GitHub identity gate failed: '$login'"
}

$head = (git -c 'safe.directory=*' -C $repo rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0 -or $head -ne $expectedControl) {
  throw "Unexpected local HEAD: '$head'"
}

git -c 'safe.directory=*' -C $repo merge-base --is-ancestor $expectedParent $expectedControl
if ($LASTEXITCODE -ne 0) {
  throw 'Control checkpoint is not a descendant of the published parent'
}

$changed = @(git -c 'safe.directory=*' -C $repo diff --name-only "$expectedParent..$expectedControl")
if ($LASTEXITCODE -ne 0 -or $changed.Count -ne 1 -or $changed[0] -ne $expectedPath) {
  throw "Unexpected control diff: $($changed -join ', ')"
}

$remoteBeforeLine = (git -c 'safe.directory=*' -C $repo ls-remote $remote "refs/heads/$branch").Trim()
if ($LASTEXITCODE -ne 0) {
  throw 'Could not read remote branch'
}
$remoteBefore = ($remoteBeforeLine -split '\s+')[0]
if ($remoteBefore -ne $expectedParent) {
  throw "Remote moved: expected $expectedParent, found $remoteBefore"
}

git -c 'safe.directory=*' -C $repo push $remote "$expectedControl`:refs/heads/$branch"
if ($LASTEXITCODE -ne 0) {
  throw 'Fast-forward push failed'
}

$remoteAfterLine = (git -c 'safe.directory=*' -C $repo ls-remote $remote "refs/heads/$branch").Trim()
$remoteAfter = ($remoteAfterLine -split '\s+')[0]
if ($LASTEXITCODE -ne 0 -or $remoteAfter -ne $expectedControl) {
  throw "Remote verification failed: '$remoteAfter'"
}

gh workflow run $workflow `
  --repo lluiseriksson/THE-ERIKSSON-PROGRAMME `
  --ref $branch `
  -f cold=true
if ($LASTEXITCODE -ne 0) {
  throw 'Terminal workflow dispatch failed'
}

Start-Sleep -Seconds 3
$run = gh run list `
  --repo lluiseriksson/THE-ERIKSSON-PROGRAMME `
  --workflow $workflow `
  --branch $branch `
  --event workflow_dispatch `
  --limit 10 `
  --json databaseId,headSha,status,url,createdAt |
  ConvertFrom-Json |
  Where-Object { $_.headSha -eq $expectedControl } |
  Sort-Object createdAt -Descending |
  Select-Object -First 1

if ($null -eq $run) {
  throw 'Dispatch returned but no matching run was found'
}

Write-Host 'UNIFORM_B0_TERMINAL_DISPATCH_OK'
Write-Host "CONTROL_SHA=$expectedControl"
Write-Host "SOURCE_SHA=73bb1a2008c557840a91e50d8abe6b874947f7ee"
Write-Host "RUN_ID=$($run.databaseId)"
Write-Host "RUN_STATUS=$($run.status)"
Write-Host "RUN_URL=$($run.url)"
