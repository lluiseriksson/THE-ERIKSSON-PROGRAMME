# c5_release_check.ps1 — the authoritative C5 pre-tag check sequence.
# REGISTERED BEFORE THE FINAL RUN (v2: pre-run correction, own commit —
# v1 used `exit` inside Step scriptblocks, which in PowerShell
# terminates the whole script; steps now RETURN booleans).  Run from a
# CLEAN CLONE checked out at the candidate release revision; the
# transcript (full stdout) is committed with the release commit.  Any
# FAIL = full stop + autopsy; no re-runs without a diagnosis commit.
#
# Usage:  powershell -File scripts\c5_release_check.ps1
# Env: C5_PYTHON (default C:\Python312\python.exe, needs python-flint
# 0.9.0), C5_TECTONIC (no system TeX on this box; tectonic 0.15.0
# lives in a session scratchpad — standing toolchain note).

$ErrorActionPreference = 'Continue'
$py = if ($env:C5_PYTHON) { $env:C5_PYTHON } else { 'C:\Python312\python.exe' }
$tectonic = if ($env:C5_TECTONIC) { $env:C5_TECTONIC } else { 'tectonic' }
$script:fail = @()

function Step($name, [scriptblock]$body) {
    Write-Host "=== C5-RELEASE-CHECK: $name ==="
    $ok = $false
    try { $ok = [bool](& $body) } catch { Write-Host "exception: $_"; $ok = $false }
    if ($ok) { Write-Host "--- OK: $name" }
    else { Write-Host "### FAIL: $name"; $script:fail += $name }
}

Write-Host "C5 release check at revision: $(git rev-parse HEAD)"
$dirty = git status --porcelain
if ($dirty) {
    Write-Host "### FAIL: dirty worktree — release checks run from a clean clone only"
    Write-Host $dirty
    exit 1
}
Write-Host "worktree: clean"

# 0. Pins agree
Step 'toolchain-pin' {
    $tc = (Get-Content lean-toolchain -Raw).Trim()
    Write-Host "lean-toolchain: $tc"
    $tc -eq 'leanprover/lean4:v4.29.0-rc6'
}
Step 'mathlib-pin' {
    $pin = '07642720480157414db592fa85b626dafb71355b'
    $lf = Select-String -Path lakefile.lean -Pattern $pin -Quiet
    $mf = Select-String -Path lake-manifest.json -Pattern $pin -Quiet
    Write-Host "lakefile: $lf  manifest: $mf"
    $lf -and $mf
}

# 1. Build (expect GREEN; job count recorded in this transcript)
Step 'lake-cache' { lake exe cache get | Out-Host; $LASTEXITCODE -eq 0 }
Step 'lake-build-AmosClosure' { lake build AmosClosure | Out-Host; $LASTEXITCODE -eq 0 }

# 2. Oracle (expect 110 x [propext, Classical.choice, Quot.sound])
Step 'axiom-oracle' {
    $out = lake env lean AmosClosure/Oracle.lean 2>&1
    $out | Out-Host
    if ($LASTEXITCODE -ne 0) { return $false }
    $clean = ($out | Select-String -SimpleMatch '[propext, Classical.choice, Quot.sound]').Count
    $axline = ($out | Select-String -SimpleMatch "' depends on axioms:").Count
    Write-Host "clean-oracle lines: $clean of $axline axiom reports (expect 110/110)"
    ($clean -eq 110) -and ($axline -eq 110)
}

# 3. Certified companion (expect 30/30 PASS, 0 UNDECIDED, 0 FAIL)
Step 'certified-companion' {
    $out = & $py scripts/c5_crossing_arb.py 2>&1
    $out | Out-Host
    if ($LASTEXITCODE -ne 0) { return $false }
    [bool]($out | Select-String -SimpleMatch 'PASS 30 / FAIL 0 / UNDECIDED 0')
}

# 4. Manuscript compiles
Step 'tectonic-compile' { & $tectonic -X compile papers/c5-crossing/c5_crossing.tex | Out-Host; $LASTEXITCODE -eq 0 }

# 5. Canonical hashes (record; compare against RELEASE-MANIFEST.md;
#    tex from the git blob, never worktree bytes)
Step 'artifact-hashes' {
    # step 4 recompiles the pdf in the worktree (timestamp
    # nondeterminism); canonical hashes come from the COMMITTED blobs
    cmd /c "git show HEAD:papers/c5-crossing/c5_crossing.tex > %TEMP%\c5_tex_blob"
    cmd /c "git show HEAD:papers/c5-crossing/c5_crossing.pdf > %TEMP%\c5_pdf_blob"
    cmd /c "git show HEAD:scripts/c5_crossing_arb.py > %TEMP%\c5_py_blob"
    cmd /c "git show HEAD:scripts/c5_crossing_arb_transcript.txt > %TEMP%\c5_tr_blob"
    Write-Host "tex        sha256 (LF blob): $((Get-FileHash "$env:TEMP\c5_tex_blob" -Algorithm SHA256).Hash)"
    Write-Host "pdf        sha256 (blob):    $((Get-FileHash "$env:TEMP\c5_pdf_blob" -Algorithm SHA256).Hash)"
    Write-Host "script     sha256 (blob):    $((Get-FileHash "$env:TEMP\c5_py_blob" -Algorithm SHA256).Hash)"
    Write-Host "transcript sha256 (blob):    $((Get-FileHash "$env:TEMP\c5_tr_blob" -Algorithm SHA256).Hash)"
    $true
}

if ($script:fail.Count -gt 0) {
    Write-Host "### C5 RELEASE CHECK: FAIL ($($script:fail -join ', '))"
    exit 1
}
Write-Host '=== C5 RELEASE CHECK: ALL GREEN ==='
exit 0
