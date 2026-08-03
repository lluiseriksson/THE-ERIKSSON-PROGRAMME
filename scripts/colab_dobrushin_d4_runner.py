#!/usr/bin/env python3
"""Colab runner for D-4a and the core wiring.  Linux, CPU / high-RAM, never GPU.

Owner's rule of 2026-08-01: Colab is the sanctioned compilation plane.  Nothing
here pushes; no token is read or written.  Same sentinel protocol as the D-1
and D-3 runners.

  stage 0  environment — SHA, toolchain, Mathlib pin; FAILS on mismatch.
  stage 1  certifiers, BEFORE any build: judge_dobrushin_d4.py (G12–G14, the
           gates of this rung) plus re-runs of d3/d3b, each in `normal` and
           `optimized`.
  stage 2  Lean: the lane modules `DobrushinGibbs` and `DobrushinIsing` by name.
  stage 3  THE CORE, with the six D-3/D-4 modules wired into
           `YangMillsCore.lean`.  Prediction, CORRECTED before this
           measurement: the original 8468 -> 8473 used the lane's own earlier
           count as base, but the branch base (paper 14's anchor) already
           carries `SpatialReconstruction`, measured at **8469**.  The
           corrected expectation with six new modules is therefore
           **8475 jobs**.  The tail of the build log is printed so the
           count is read from the artefact, not remembered.
  stage 4  the FULL repository oracle (`oracle_check.lean`), now carrying the
           D-3/D-4 declarations.
  stage 5  hashes of everything that travels back.

SENTINELS: one line, the child's real decimal exit code, written atomically and
validated; only zero plus a log permits a PASS candidate.
"""

import hashlib
import os
import re
import subprocess
import sys

REPO = "/content/eriksson"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
EXPECTED_MATHLIB_PIN = "07642720480157414db592fa85b626dafb71355b"
LANE_MODULES = ["YangMills.OS.DobrushinGibbs", "YangMills.OS.DobrushinIsing",
                "YangMills.OS.DobrushinLattice"]
CERTIFIERS = ["scripts/judge_dobrushin_d5.py",
              "scripts/judge_dobrushin_d4.py",
              "scripts/judge_dobrushin_d3.py",
              "scripts/judge_dobrushin_d3b.py"]
OUT = "/content/artefacts"

SENTINEL_ABSENT = "absent"
SENTINEL_MALFORMED = "malformed"
SENTINEL_NONZERO = "nonzero"
SENTINEL_ZERO = "zero"


def write_sentinel(path, code):
    tmp = path + ".writing"
    with open(tmp, "w", encoding="ascii") as f:
        f.write(f"{int(code)}\n")
        f.flush()
        os.fsync(f.fileno())
    with open(tmp, encoding="ascii") as f:
        body = f.read().strip()
    if not body or re.fullmatch(r"-?\d+", body) is None:
        os.remove(tmp)
        raise SystemExit(f"FATAL: refusing to publish a malformed sentinel for {path}")
    os.replace(tmp, path)


def read_sentinel(path):
    if not os.path.exists(path):
        return SENTINEL_ABSENT, None
    with open(path, encoding="ascii") as f:
        body = f.read().strip()
    if not body or re.fullmatch(r"-?\d+", body) is None:
        return SENTINEL_MALFORMED, body
    code = int(body)
    return (SENTINEL_ZERO if code == 0 else SENTINEL_NONZERO), code


def run(cmd, name, mode, cwd=REPO, env=None):
    os.makedirs(OUT, exist_ok=True)
    log = os.path.join(OUT, f"{name}.{mode}.log")
    sen = os.path.join(OUT, f"{name}.{mode}.sentinel")
    print(f"  -> {name} [{mode}] : {' '.join(cmd)}", flush=True)
    with open(log, "w", encoding="utf-8", errors="replace") as lf:
        p = subprocess.run(cmd, cwd=cwd, stdout=lf, stderr=subprocess.STDOUT,
                           env=env)
    write_sentinel(sen, p.returncode)
    state, code = read_sentinel(sen)
    print(f"     sentinel: {state} ({code})   log: {log}", flush=True)
    return state, code, log


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def stage0(expected_sha):
    print("stage 0 — environment")
    sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=REPO,
                         capture_output=True, text=True).stdout.strip()
    tc = open(os.path.join(REPO, "lean-toolchain"), encoding="utf-8").read().strip()
    manifest = open(os.path.join(REPO, "lake-manifest.json"), encoding="utf-8").read()
    pin_ok = EXPECTED_MATHLIB_PIN in manifest
    print(f"  repo SHA        : {sha}")
    print(f"  toolchain       : {tc}")
    print(f"  mathlib pin     : {'found' if pin_ok else 'NOT FOUND'}")
    problems = []
    if expected_sha and sha != expected_sha:
        problems.append(f"repo SHA {sha} != expected {expected_sha}")
    if tc != EXPECTED_TOOLCHAIN:
        problems.append(f"toolchain {tc} != expected {EXPECTED_TOOLCHAIN}")
    if not pin_ok:
        problems.append("Mathlib pin absent from lake-manifest.json")
    if problems:
        for p in problems:
            print(f"  MISMATCH: {p}")
        raise SystemExit("FATAL stage 0 — wrong environment")
    print("  stage 0 OK")
    return sha


def stage1():
    print("stage 1 — certifiers, BEFORE any build")
    results = {}
    for script in CERTIFIERS:
        base = os.path.basename(script).replace(".py", "")
        for mode, argv in (("normal", [sys.executable, script]),
                           ("optimized", [sys.executable, "-O", script])):
            results[(base, mode)] = run(argv, base, mode)
    return results


def stage2():
    print("stage 2 — the new lane module")
    out = {}
    for m in LANE_MODULES:
        out[m] = run(["lake", "build", m], m.replace(".", "_"), "normal")
    return out


def stage3():
    print("stage 3 — the core, with the six lane modules wired in")
    res = run(["lake", "build", "YangMillsCore"], "YangMillsCore", "normal")
    log = res[2]
    try:
        with open(log, encoding="utf-8", errors="replace") as f:
            tail = f.readlines()[-5:]
        print("  core log tail:")
        for line in tail:
            print("    " + line.rstrip())
    except OSError:
        print("  (could not read core log tail)")
    return res


def stage4():
    print("stage 4 — the FULL repository oracle")
    return run(["lake", "env", "lean", "oracle_check.lean"], "oracle_full", "normal")


def stage5(sha):
    print("stage 5 — hashes")
    rows = []
    for f in ["YangMills/OS/DobrushinGibbs.lean",
              "YangMills/OS/DobrushinIsing.lean",
              "YangMills/OS/DobrushinLattice.lean",
              "YangMillsCore.lean",
              "oracle_check.lean",
              "scripts/judge_dobrushin_d4.py",
              "scripts/colab_dobrushin_d4_runner.py"]:
        p = os.path.join(REPO, f)
        if os.path.exists(p):
            rows.append((f, sha256_file(p), os.path.getsize(p)))
    print(f"  repo SHA {sha}")
    for f, h, n in rows:
        print(f"  {h}  {n:>8}  {f}")
    return rows


def summarise(all_results):
    print()
    print("=" * 74)
    bad = []
    for key, (state, code, log) in all_results.items():
        tag = key if isinstance(key, str) else f"{key[0]} [{key[1]}]"
        print(f"  {tag:<48} {state} ({code})")
        if state != SENTINEL_ZERO:
            bad.append(tag)
    print("=" * 74)
    if bad:
        print(f"RUN VERDICT: FAIL — {len(bad)} child(ren) not zero: {', '.join(bad)}")
        return 1
    print("RUN VERDICT: every child exited zero.  This is a PASS CANDIDATE, not "
          "a PASS: the logs still have to be read.")
    return 0


def main():
    expected_sha = sys.argv[1] if len(sys.argv) > 1 else None
    sha = stage0(expected_sha)
    results = {}
    results.update(stage1())
    results.update(stage2())
    results["YangMillsCore"] = stage3()
    results["oracle_full"] = stage4()
    stage5(sha)
    return summarise(results)


if __name__ == "__main__":
    sys.exit(main())
