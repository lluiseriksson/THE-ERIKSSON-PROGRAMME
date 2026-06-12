<#
.SYNOPSIS
    Final cleanup + push: keep the VERIFIED YangMillsCore, remove the sprawl, push a branch.

.DESCRIPTION
    Updated 2026-05-29, after `lake build YangMillsCore` was confirmed GREEN
    (8185 jobs) with a clean oracle on every new result. The core's import closure
    was therefore proven independent of the sprawl, so removing the sprawl cannot
    break the core build.

    SAFETY (do not skip):
      * Everything happens on a branch — `main` is left untouched and every
        deletion is recoverable from git history.
      * `lake build YangMillsCore` is run as a GATE both BEFORE deleting (must be
        green to proceed) and AFTER deleting (must still be green to commit).
        If the post-deletion build fails, the script ABORTS WITHOUT COMMITTING and
        tells you how to back out — nothing is pushed.

    Steps: branch → build-gate → git rm sprawl → rewire YangMills.lean → rebuild
    gate → commit → push.  Review before running.  `-WhatIf` previews deletions.
#>

[CmdletBinding(SupportsShouldProcess = $true)]
param(
    [string]$Branch = "verified-core-cleanup",
    [switch]$SkipPush
)

# NOTE: must be "Continue", not "Stop": git and lake write progress/warnings to
# stderr, and under "Stop" PowerShell would treat that as a terminating error and
# abort the script. We gate on $LASTEXITCODE explicitly instead.
$ErrorActionPreference = "Continue"
$RepoRoot = Split-Path -Parent $PSScriptRoot
Set-Location $RepoRoot
Write-Host "==> Repo root: $RepoRoot" -ForegroundColor Cyan

function Build-Core($label) {
    Write-Host "==> [$label] lake build YangMillsCore" -ForegroundColor Cyan
    lake build YangMillsCore
    return ($LASTEXITCODE -eq 0)
}

# --- 1. Sanity --------------------------------------------------------------
if (-not (Test-Path "$RepoRoot\YangMillsCore.lean")) {
    Write-Host "ABORT: not in the repo root (no YangMillsCore.lean)." -ForegroundColor Red; exit 1
}

# --- 2. Branch (carries the uncommitted new files with it) ------------------
$branchExists = (git branch --list $Branch | Out-String).Trim()
if ($branchExists) { git switch $Branch } else { git switch -c $Branch }
if ($LASTEXITCODE -ne 0) { Write-Host "ABORT: git switch failed." -ForegroundColor Red; exit 1 }

# --- 3. BUILD GATE (before any deletion) ------------------------------------
if (-not (Build-Core "pre-delete gate")) {
    Write-Host "ABORT: core does not build even before deletion. Nothing removed." -ForegroundColor Red
    exit 1
}
Write-Host "==> Core GREEN. Proceeding to remove the sprawl." -ForegroundColor Green

# --- 4. The discard set -----------------------------------------------------
# Whole directories that route only to the vacuous target / LSI-Balaban sprawl.
$DiscardDirs = @(
    "YangMills\ClayCore\BalabanRG",
    "YangMills\L2_Balaban", "YangMills\L3_RGIteration",
    "YangMills\L4_LargeField", "YangMills\L4_WilsonLoops", "YangMills\L4_TransferMatrix",
    "YangMills\L5_MassGap", "YangMills\L5_KPDecay",
    "YangMills\L6_FeynmanKac", "YangMills\L6_OS",
    "YangMills\L7_Continuum", "YangMills\L8_Terminal",
    "YangMills\P2_MaxEntClustering", "YangMills\P3_BalabanRG", "YangMills\P4_Continuum",
    "YangMills\P5_KPDecay", "YangMills\P6_AsymptoticFreedom", "YangMills\P7_SpectralGap"
)

# ClayCore root files in the vacuous-target chain (NOT imported by YangMillsCore).
$DiscardClayCoreFiles = @(
    "YangMills\ClayCore\AbelianU1Witness.lean",
    "YangMills\ClayCore\ClayWitness.lean",
    "YangMills\ClayCore\ClayAuthentic.lean",
    "YangMills\ClayCore\KPSmallness.lean",
    "YangMills\ClayCore\ClayTheorem.lean"
)

# Root scratch / build-verification artifacts.
$DiscardFiles = @(
    "Test.lean", "TestC71Full.lean", "TestC72Proto.lean", "OracleC69.lean", "OracleC96.lean",
    "README.proposed.md", "run_build.bat", "build_log.txt"
)

# P8_PhysicalGap: delete everything EXCEPT the three salvaged core modules.
$P8Keep = @("SUN_Compact.lean", "SUN_StateConstruction.lean", "MemLpLogIntegrability.lean")

function Remove-Path($rel) {
    $full = Join-Path $RepoRoot $rel
    if (-not (Test-Path $full)) { return }
    if ($PSCmdlet.ShouldProcess($full, "git rm -r")) {
        git rm -r -q -- "$rel" 2>$null
        if ($LASTEXITCODE -ne 0 -and (Test-Path $full)) { Remove-Item -Recurse -Force $full }
    } else { Write-Host "    [WhatIf] would remove $rel" -ForegroundColor DarkYellow }
}

function Remove-DirExcept($relDir, $keep) {
    $full = Join-Path $RepoRoot $relDir
    if (-not (Test-Path $full)) { return }
    Get-ChildItem -Path $full -Recurse -File | ForEach-Object {
        if ($keep -notcontains $_.Name) {
            $rel = $_.FullName.Substring($RepoRoot.Length + 1)
            if ($PSCmdlet.ShouldProcess($_.FullName, "git rm")) {
                git rm -q -- "$rel" 2>$null
                if ($LASTEXITCODE -ne 0) { Remove-Item -Force $_.FullName }
            } else { Write-Host "    [WhatIf] would remove $rel" -ForegroundColor DarkYellow }
        }
    }
}

Write-Host "==> Removing discard directories" -ForegroundColor Cyan
foreach ($d in $DiscardDirs) { Remove-Path $d }
Write-Host "==> Removing vacuous-chain ClayCore files" -ForegroundColor Cyan
foreach ($f in $DiscardClayCoreFiles) { Remove-Path $f }
Write-Host "==> Removing root scratch files" -ForegroundColor Cyan
foreach ($f in $DiscardFiles) { Remove-Path $f }
Write-Host "==> Pruning P8_PhysicalGap (keeping the 3 core modules)" -ForegroundColor Cyan
Remove-DirExcept "YangMills\P8_PhysicalGap" $P8Keep

if ($WhatIfPreference) { Write-Host "==> -WhatIf set: stopping before rewire/build/commit." -ForegroundColor Yellow; exit 0 }

# --- 5. Rewire the old root aggregator --------------------------------------
$YMRoot = Join-Path $RepoRoot "YangMills.lean"
Write-Host "==> Rewiring YangMills.lean -> import YangMillsCore" -ForegroundColor Cyan
@"
/- Root aggregator.  The sound, self-contained, compiler-verified development now
   lives in `YangMillsCore`.  See `README.md`, `HORIZON.md`, `CLEANUP_PLAN.md`.
   Build with:  lake build YangMillsCore -/
import YangMillsCore
"@ | Set-Content -Path $YMRoot -Encoding UTF8
git add -- "YangMills.lean" 2>$null

# --- 6. REBUILD GATE (after deletion) ---------------------------------------
if (-not (Build-Core "post-delete gate")) {
    Write-Host "ABORT: core build FAILED after deletion. NOT committing, NOT pushing." -ForegroundColor Red
    Write-Host "       A required file was probably removed. Back out with:" -ForegroundColor Red
    Write-Host "         git restore --staged . ; git checkout -- . ; git switch main" -ForegroundColor Red
    exit 1
}
Write-Host "==> Core still GREEN after cleanup." -ForegroundColor Green

# --- 7. Commit --------------------------------------------------------------
git add -A
git commit -m "Verified sound core + remove LSI/Balaban sprawl

YangMillsCore builds green (lake build YangMillsCore) with oracle
[propext, Classical.choice, Quot.sound] on every result. New, compiler-verified:
  - centre-eigenfunction engine (SU(N)) + general left-invariant engine
  - Z_N selection rules: trace, powers, mixed moments, matrix-coefficient
    monomials, Newton power sums, and the bigraded (covariance) rule
  - SU(1) triviality (boundary case) and exact U(1) Fourier orthogonality
Removed: BalabanRG (~150 files), L2-L8 / P2-P7 LSI pipeline, the vacuous-target
chain, ~25 BFS-dead axioms, root scratch. Rewired YangMills.lean -> YangMillsCore.
See README.md / HORIZON.md / FOUNDATIONS.md / CLEANUP_PLAN.md."
if ($LASTEXITCODE -ne 0) { Write-Host "Note: commit returned nonzero (maybe nothing to commit)." -ForegroundColor Yellow }

if ($SkipPush) { Write-Host "==> -SkipPush set. Committed locally on '$Branch'. Not pushed." -ForegroundColor Yellow; exit 0 }

# --- 8. Push ----------------------------------------------------------------
Write-Host "==> Pushing branch $Branch" -ForegroundColor Cyan
git push -u origin $Branch
if ($LASTEXITCODE -ne 0) { Write-Host "ABORT: git push failed (auth?)." -ForegroundColor Red; exit 1 }

Write-Host ""
Write-Host "DONE. main is untouched. Open a PR / merge with:" -ForegroundColor Green
Write-Host "  https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/compare/main...$Branch?expand=1" -ForegroundColor Green
Write-Host "  (or:  git switch main; git merge $Branch; git push )" -ForegroundColor Green
