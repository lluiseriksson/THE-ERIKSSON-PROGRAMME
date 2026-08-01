#!/usr/bin/env python3
"""Colab runner for the Dobrushin lane.  Linux, CPU / high-RAM, never GPU.

Owner's rule of 2026-08-01: this is the sanctioned compilation plane.  Nothing
in this file pushes, and no GitHub token is read or written.  Artefacts and
their hashes are printed for verification back on the desktop; only there are
they committed.

  stage 0  environment — repo SHA, toolchain, Mathlib pin.  FAILS HERE on any
           mismatch rather than compiling against a stale cache.
  stage 1  the certifiers, in BOTH `normal` and `optimized` modes
  stage 2  Lean: build the two lane modules, then the full core for the job count
  stage 3  the oracle
  stage 4  hashes of everything that will travel back

SENTINELS.  Existence never means success.  Each sentinel holds exactly one
line: the child's real decimal exit code, captured after it terminated and
written atomically (temp file, flush, fsync, non-empty and integer-parse
validation, rename).  Four states are distinguished on read: absent / empty or
non-integer / non-zero integer / zero integer.  Only a zero integer, together
with a log that was actually produced, permits a PASS candidate.  Logs and
sentinels are named by the semantic mode, never by an indistinguishable numeric
suffix.
"""

import hashlib
import os
import re
import subprocess
import sys

REPO = "/content/eriksson"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
EXPECTED_MATHLIB_PIN = "07642720480157414db592fa85b626dafb71355b"
LANE_MODULES = [
    "YangMills.OS.DobrushinMatrix",
    "YangMills.OS.DobrushinCoefficient",
]
CERTIFIERS = ["scripts/judge_dobrushin.py", "scripts/judge_dobrushin_d2.py"]
OUT = "/content/artefacts"

SENTINEL_ABSENT = "absent"
SENTINEL_MALFORMED = "malformed"
SENTINEL_NONZERO = "nonzero"
SENTINEL_ZERO = "zero"


def write_sentinel(path, code):
    """Atomic, validated, one decimal line."""
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
    """Run one child, log under its semantic mode name, sentinel its real exit."""
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


# ---------------------------------------------------------------- stage 0
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
        problems.append(f"Mathlib pin {EXPECTED_MATHLIB_PIN} absent from lake-manifest.json")
    if problems:
        for p in problems:
            print(f"  MISMATCH: {p}")
        raise SystemExit("FATAL stage 0 — refusing to compile against an "
                         "environment that is not the one this lane pinned")
    print("  stage 0 OK")
    return sha


# ---------------------------------------------------------------- stage 1
def stage1():
    """Certifiers in BOTH modes.  A gate that behaves differently under -O is a
    gate that can be deleted by a flag."""
    print("stage 1 — certifiers, normal and optimized")
    results = {}
    for script in CERTIFIERS:
        base = os.path.basename(script).replace(".py", "")
        for mode, argv in (("normal", [sys.executable, script]),
                           ("optimized", [sys.executable, "-O", script])):
            results[(base, mode)] = run(argv, base, mode)
    return results


# ---------------------------------------------------------------- stage 2/3
def stage2():
    print("stage 2 — Lean")
    out = {}
    for m in LANE_MODULES:
        out[m] = run(["lake", "build", m], m.replace(".", "_"), "normal")
    out["YangMillsCore"] = run(["lake", "build", "YangMillsCore"],
                               "YangMillsCore", "normal")
    return out


def stage3():
    print("stage 3 — oracle")
    return run(["lake", "env", "lean", "oracle_check.lean"], "oracle", "normal")


# ---------------------------------------------------------------- stage 4
def stage4(sha):
    print("stage 4 — hashes")
    rows = []
    for f in ["YangMills/OS/DobrushinMatrix.lean",
              "YangMills/OS/DobrushinCoefficient.lean",
              "scripts/judge_dobrushin.py",
              "scripts/judge_dobrushin_d2.py"]:
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
    results["oracle"] = stage3()
    stage4(sha)
    return summarise(results)


if __name__ == "__main__":
    sys.exit(main())
