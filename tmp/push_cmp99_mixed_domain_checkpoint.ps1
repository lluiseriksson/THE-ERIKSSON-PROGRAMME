$ErrorActionPreference = 'Stop'

$repo = 'C:\Users\lluis\Documents\Codex\2026-07-12\pu\work\THE-ERIKSSON-PROGRAMME-wilson-hessian'
$branch = 'refs/heads/codex/cmp116-interacting-wilson-hessian'
$expectedRemote = '386c3c7e15702b56f82e29b227d9d3601d1feb89'
$expectedLocal = '8bc10499f0777dc0efa605179093329402efdf35'

Write-Host '== Publicacion fail-closed: mixed-domain + orientation PRE-VALIDATION =='
Write-Host 'No usa force-push, no cambia checkout y no lanza CI.'

gh auth status --hostname github.com
if ($LASTEXITCODE -ne 0) { throw 'GH_AUTH_INVALID' }

$local = git -c 'safe.directory=*' -C $repo rev-parse HEAD
if ($LASTEXITCODE -ne 0 -or $local.Trim() -ne $expectedLocal) {
  throw "LOCAL_HEAD_MISMATCH actual=$local expected=$expectedLocal"
}

$remoteLine = git -c 'safe.directory=*' -C $repo ls-remote github $branch
if ($LASTEXITCODE -ne 0) { throw 'REMOTE_READ_FAILED' }
$remote = ($remoteLine -split "`t")[0]
if ($remote -ne $expectedRemote) {
  throw "REMOTE_HEAD_MISMATCH actual=$remote expected=$expectedRemote"
}

git -c 'safe.directory=*' -C $repo merge-base --is-ancestor $expectedRemote $expectedLocal
if ($LASTEXITCODE -ne 0) { throw 'NOT_FAST_FORWARD' }

git -c 'safe.directory=*' -C $repo push github "${expectedLocal}:${branch}"
if ($LASTEXITCODE -ne 0) { throw 'PUSH_FAILED' }

$verifyLine = git -c 'safe.directory=*' -C $repo ls-remote github $branch
if ($LASTEXITCODE -ne 0) { throw 'REMOTE_VERIFY_FAILED' }
$verify = ($verifyLine -split "`t")[0]
if ($verify -ne $expectedLocal) {
  throw "REMOTE_POST_PUSH_MISMATCH actual=$verify expected=$expectedLocal"
}

Write-Host 'CMP99_MIXED_DOMAIN_CHECKPOINT_PUSH_OK'
Write-Host "REMOTE_HEAD=$verify"
