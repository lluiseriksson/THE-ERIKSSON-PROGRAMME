$ErrorActionPreference = 'Stop'
Set-StrictMode -Version Latest

$repo = (Resolve-Path -LiteralPath (Join-Path $PSScriptRoot '..')).Path
$branch = 'codex/cmp116-interacting-wilson-hessian'
$expectedRemote = '59b2ddf5a34d4cd52dc54a617b53975124ca45f6'
$expectedLocal = 'a754e28555270ebbdab8bff05f262368a39c43fa'

Write-Host '== Publicación fail-closed del retry B0 =='
Write-Host 'No usa force-push, no cambia checkout y no lanza CI.'

gh auth status --hostname github.com
if ($LASTEXITCODE -ne 0) {
  throw 'GH_AUTH_NOT_READY'
}

gh auth setup-git
if ($LASTEXITCODE -ne 0) {
  throw 'GH_SETUP_GIT_FAILED'
}

$local = (git -c 'safe.directory=*' -C $repo rev-parse HEAD).Trim()
if ($LASTEXITCODE -ne 0 -or $local -ne $expectedLocal) {
  throw "LOCAL_HEAD_MISMATCH expected=$expectedLocal actual=$local"
}

$row = git -c 'safe.directory=*' -C $repo ls-remote github "refs/heads/$branch"
if ($LASTEXITCODE -ne 0) {
  throw 'REMOTE_READ_FAILED'
}
$remote = (($row -split '\s+')[0]).Trim()
if ($remote -ne $expectedRemote) {
  throw "REMOTE_HEAD_MISMATCH expected=$expectedRemote actual=$remote"
}

git -c 'safe.directory=*' -C $repo merge-base --is-ancestor $remote $local
if ($LASTEXITCODE -ne 0) {
  throw 'NON_FAST_FORWARD_HISTORY'
}

git -c 'safe.directory=*' -C $repo push github `
  "${local}:refs/heads/$branch"
if ($LASTEXITCODE -ne 0) {
  throw 'PUSH_FAILED'
}

$verifyRow = git -c 'safe.directory=*' -C $repo ls-remote github "refs/heads/$branch"
if ($LASTEXITCODE -ne 0) {
  throw 'REMOTE_VERIFY_FAILED'
}
$verified = (($verifyRow -split '\s+')[0]).Trim()
if ($verified -ne $expectedLocal) {
  throw "REMOTE_VERIFY_MISMATCH expected=$expectedLocal actual=$verified"
}

Write-Host 'UNIFORM_B0_RETRY_PUSH_OK'
Write-Host "REMOTE_HEAD=$verified"
