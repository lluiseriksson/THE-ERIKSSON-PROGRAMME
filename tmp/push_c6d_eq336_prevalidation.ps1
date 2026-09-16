$ErrorActionPreference = 'Stop'

$repo = 'C:\Users\lluis\Documents\Codex\2026-07-12\pu\work\THE-ERIKSSON-PROGRAMME-wilson-hessian'
$branch = 'codex/cmp116-interacting-wilson-hessian'
$expectedRemote = 'a754e28555270ebbdab8bff05f262368a39c43fa'
$expectedHead = 'c84ec69257fccadb421d3e734e94b6061e411129'

Write-Host '== Publicación fail-closed del checkpoint PRE-VALIDATION C6d ==' -ForegroundColor Cyan
Write-Host 'No usa force-push, no cambia checkout y no lanza CI.'

$auth = gh auth status --hostname github.com 2>&1 | Out-String
if ($LASTEXITCODE -ne 0) { throw "gh auth status failed:`n$auth" }
if ($auth -notmatch 'account lluiseriksson') {
  throw "GitHub account is not lluiseriksson:`n$auth"
}

$head = git -c 'safe.directory=*' -C $repo rev-parse HEAD
if ($LASTEXITCODE -ne 0 -or $head.Trim() -ne $expectedHead) {
  throw "Unexpected local HEAD: $head"
}

$remoteLine = git -c 'safe.directory=*' -C $repo ls-remote github "refs/heads/$branch"
if ($LASTEXITCODE -ne 0) { throw 'Unable to read remote branch' }
$remoteHead = ($remoteLine -split '\s+')[0]
if ($remoteHead -ne $expectedRemote) {
  throw "Unexpected remote HEAD: $remoteHead (expected $expectedRemote)"
}

git -c 'safe.directory=*' -C $repo merge-base --is-ancestor $expectedRemote $expectedHead
if ($LASTEXITCODE -ne 0) { throw 'Expected remote is not an ancestor of the checkpoint' }

$changed = @(git -c 'safe.directory=*' -C $repo diff --name-only "$expectedRemote..$expectedHead")
$expected = @(
  '.github/workflows/validate-localized-carrier.yml',
  'tmp/BalabanCMP99Eq336PhysicalDStarDRegularityClass.draft.lean',
  'tmp/BalabanCMP99Eq336PhysicalDStarDRegularityClassAudit.draft.lean',
  'tmp/CMP99DStarPairSummationByPartsRepro.lean',
  'scripts/colab_c6d_eq336_adjoint_debug_validation.py',
  'scripts/colab_c6d_eq336_adjoint_debug_validation.ipynb'
)
$unexpected = @($changed | Where-Object { $_ -notin $expected })
$missing = @($expected | Where-Object { $_ -notin $changed })
if ($unexpected.Count -ne 0 -or $missing.Count -ne 0) {
  throw "Checkpoint path gate failed. Unexpected=[$($unexpected -join ', ')] Missing=[$($missing -join ', ')]"
}

git -c 'safe.directory=*' -C $repo push github "$expectedHead`:refs/heads/$branch"
if ($LASTEXITCODE -ne 0) { throw 'Fast-forward push failed' }

$verifyLine = git -c 'safe.directory=*' -C $repo ls-remote github "refs/heads/$branch"
if ($LASTEXITCODE -ne 0) { throw 'Unable to verify remote branch after push' }
$verifyHead = ($verifyLine -split '\s+')[0]
if ($verifyHead -ne $expectedHead) {
  throw "Remote verification failed: $verifyHead"
}

Write-Host 'C6D_EQ336_PREVALIDATION_PUSH_OK' -ForegroundColor Green
Write-Host "REMOTE_HEAD=$verifyHead"
