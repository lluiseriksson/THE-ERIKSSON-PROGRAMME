$ErrorActionPreference = 'Stop'

$repo = 'C:\Users\lluis\Documents\Codex\2026-07-12\pu\work\THE-ERIKSSON-PROGRAMME-wilson-hessian'
$remoteName = 'github'
$branch = 'codex/cmp116-interacting-wilson-hessian'
$workflow = 'validate-localized-carrier.yml'
$expectedRemoteBefore = 'a754e28555270ebbdab8bff05f262368a39c43fa'
$expectedControl = 'ebccd7e8811d639587563fe060705811163e1c57'

Write-Host '== Publicación y único dispatch terminal del retry B0 =='
Write-Host 'No usa force-push, no cambia checkout y no hace rerun.'

gh auth status --hostname github.com
if ($LASTEXITCODE -ne 0) { throw 'GH_AUTH_STATUS_FAILED' }
$login = (gh api user --jq .login).Trim()
if ($LASTEXITCODE -ne 0 -or $login -ne 'lluiseriksson') {
  throw "WRONG_GITHUB_LOGIN actual=$login"
}

$head = (git -c 'safe.directory=*' -C $repo rev-parse HEAD).Trim()
if ($head -ne $expectedControl) {
  throw "WRONG_LOCAL_HEAD expected=$expectedControl actual=$head"
}
$currentBranch = (git -c 'safe.directory=*' -C $repo branch --show-current).Trim()
if ($currentBranch -ne $branch) {
  throw "WRONG_BRANCH expected=$branch actual=$currentBranch"
}

$remoteLine = git -c 'safe.directory=*' -C $repo ls-remote $remoteName "refs/heads/$branch"
if ($LASTEXITCODE -ne 0 -or -not $remoteLine) { throw 'REMOTE_READ_FAILED' }
$remoteHead = ($remoteLine -split "`t")[0].Trim()
if ($remoteHead -notin @($expectedRemoteBefore, $expectedControl)) {
  throw "UNEXPECTED_REMOTE_HEAD actual=$remoteHead"
}

if ($remoteHead -eq $expectedRemoteBefore) {
  git -c 'safe.directory=*' -C $repo merge-base --is-ancestor $remoteHead $expectedControl
  if ($LASTEXITCODE -ne 0) { throw 'NON_FAST_FORWARD_PRECONDITION' }
  git -c 'safe.directory=*' -C $repo push $remoteName `
    "${expectedControl}:refs/heads/$branch"
  if ($LASTEXITCODE -ne 0) { throw 'PUSH_FAILED' }
}

$verifiedLine = git -c 'safe.directory=*' -C $repo ls-remote $remoteName "refs/heads/$branch"
$verifiedHead = ($verifiedLine -split "`t")[0].Trim()
if ($verifiedHead -ne $expectedControl) {
  throw "REMOTE_VERIFY_FAILED expected=$expectedControl actual=$verifiedHead"
}

$runs = gh run list --repo lluiseriksson/THE-ERIKSSON-PROGRAMME `
  --workflow $workflow --branch $branch --event workflow_dispatch --limit 50 `
  --json databaseId,headSha,status,conclusion,url | ConvertFrom-Json
if ($LASTEXITCODE -ne 0) { throw 'RUN_LIST_FAILED' }
$existing = @($runs | Where-Object { $_.headSha -eq $expectedControl })
if ($existing.Count -gt 0) {
  Write-Host 'UNIFORM_B0_TERMINAL_RUN_ALREADY_EXISTS'
  $existing | Select-Object databaseId,status,conclusion,url | Format-Table
  exit 0
}

gh workflow run $workflow `
  --repo lluiseriksson/THE-ERIKSSON-PROGRAMME `
  --ref $branch -f cold=true
if ($LASTEXITCODE -ne 0) { throw 'WORKFLOW_DISPATCH_FAILED' }

Write-Host 'UNIFORM_B0_TERMINAL_DISPATCH_OK'
Write-Host "CONTROL_SHA=$expectedControl"
Write-Host 'SOURCE_SHA=73bb1a2008c557840a91e50d8abe6b874947f7ee'
