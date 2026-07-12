# c5_release_check.ps1 — the authoritative C5 pre-tag check sequence.
# REGISTERED BEFORE THE FINAL RUN.  Run from a CLEAN CLONE checked out
# at the candidate release revision; the transcript (full stdout) is
# committed with the release commit.  Any FAIL = full stop + autopsy;
# no re-runs without a diagnosis commit (ghost-ledger discipline).
#
# Usage:  powershell -File scripts\c5_release_check.ps1
# Expects: lake on PATH (elan toolchain v4.29.0-rc6), python with
# python-flint 0.9.0 at C:\Python312\python.exe (override with
# $env:C5_PYTHON), tectonic on PATH.

$ErrorActionPreference = 'Stop'
$py = if ($env:C5_PYTHON) { $env:C5_PYTHON } else { 'C:\Python312\python.exe' }
# no system TeX on this box; tectonic 0.15.0 lives in a session
# scratchpad (standing toolchain note) — point C5_TECTONIC at it
$tectonic = if ($env:C5_TECTONIC) { $env:C5_TECTONIC } else { 'tectonic' }
$fail = 0

function Step($name, [scriptblock]$body) {
    Write-Host "=== C5-RELEASE-CHECK: $name ==="
    & $body
    if ($LASTEXITCODE -ne 0) {
        Write-Host "### FAIL: $name (exit $LASTEXITCODE)"
        $script:fail = 1
    } else {
        Write-Host "--- OK: $name"
    }
}

Write-Host "C5 release check at revision: $(git rev-parse HEAD)"
Write-Host "Worktree status (MUST be clean):"
git status --porcelain
if (git status --porcelain) {
    Write-Host "### FAIL: dirty worktree — release checks run from a clean clone only"
    exit 1
}

# 0. Pins agree
Step 'toolchain-pin' {
    $tc = (Get-Content lean-toolchain -Raw).Trim()
    if ($tc -ne 'leanprover/lean4:v4.29.0-rc6') { Write-Host "toolchain = $tc"; exit 1 }
    exit 0
}
Step 'mathlib-pin' {
    $pin = '07642720480157414db592fa85b626dafb71355b'
    $lf = Select-String -Path lakefile.lean -Pattern $pin -Quiet
    $mf = Select-String -Path lake-manifest.json -Pattern $pin -Quiet
    if (-not ($lf -and $mf)) { Write-Host "lakefile=$lf manifest=$mf"; exit 1 }
    exit 0
}

# 1. Build (expect GREEN; job count recorded in the transcript)
Step 'lake-cache' { lake exe cache get }
Step 'lake-build-AmosClosure' { lake build AmosClosure }

# 2. Oracle (expect 110 x [propext, Classical.choice, Quot.sound])
Step 'axiom-oracle' {
    lake env lean AmosClosure/Oracle.lean | Tee-Object -Variable oracleOut
    $bad = $oracleOut | Select-String -Pattern "'" | Where-Object {
        $_.Line -notmatch '\[propext, Classical\.choice, Quot\.sound\]' }
    $n = ($oracleOut | Select-String -Pattern '\[propext, Classical\.choice, Quot\.sound\]').Count
    Write-Host "clean-oracle lines: $n (expect 110)"
    if ($bad -or $n -ne 110) { exit 1 }
    exit 0
}

# 3. Certified companion (expect 30/30 PASS, 0 UNDECIDED, 0 FAIL)
Step 'certified-companion' { & $py scripts/c5_crossing_arb.py }

# 4. Manuscript compiles
Step 'tectonic-compile' { & $tectonic -X compile papers/c5-crossing/c5_crossing.tex }

# 5. Canonical hashes (record; compare against RELEASE-MANIFEST.md
#    and against git blobs, never worktree bytes for the tex)
Step 'artifact-hashes' {
    Write-Host "tex  (git blob): $(git show HEAD:papers/c5-crossing/c5_crossing.tex | git hash-object --stdin)"
    git show HEAD:papers/c5-crossing/c5_crossing.tex > "$env:TEMP\c5_tex_blob"
    Write-Host "tex  sha256 (LF blob): $((Get-FileHash "$env:TEMP\c5_tex_blob" -Algorithm SHA256).Hash)"
    Write-Host "pdf  sha256: $((Get-FileHash papers/c5-crossing/c5_crossing.pdf -Algorithm SHA256).Hash)"
    Write-Host "script sha256: $((Get-FileHash scripts/c5_crossing_arb.py -Algorithm SHA256).Hash)"
    Write-Host "transcript sha256: $((Get-FileHash scripts/c5_crossing_arb_transcript.txt -Algorithm SHA256).Hash)"
    exit 0
}

if ($fail -ne 0) { Write-Host '### C5 RELEASE CHECK: FAIL'; exit 1 }
Write-Host '=== C5 RELEASE CHECK: ALL GREEN ==='
