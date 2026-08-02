#!/usr/bin/env python3
"""Colab runner for the S block (spatial OS lane).  Linux, CPU / high-RAM, never GPU.

Owner's rule of 2026-08-01: this is the sanctioned compilation plane.  Nothing
in this file pushes, and no GitHub token is read or written.  Artefacts and
their hashes are printed for verification back on the desktop; only there are
they committed.

  stage 0  environment — repo SHA, toolchain, Mathlib pin.  FAILS HERE on any
           mismatch rather than compiling against a stale cache.
  stage 1  the certifiers, in BOTH `normal` and `optimized` modes
  stage 2  Lean: the lane module, then the full core
  stage 3  the oracle
  stage 4  the job count, against a prediction registered BEFORE the run
  stage 5  hashes of everything that will travel back

SENTINELS.  Existence never means success.  Each sentinel holds exactly one
line: the child's real decimal exit code, captured after it terminated and
written atomically (temp file, flush, fsync, non-empty and integer-parse
validation, rename).  Four states are distinguished on read: absent / empty or
non-integer / non-zero integer / zero integer.  Only a zero integer, together
with a log that was actually produced, permits a PASS candidate.  Logs and
sentinels are named by the semantic mode, never by an indistinguishable numeric
suffix.

THE JOB-COUNT PREDICTION, REGISTERED HERE BEFORE THE RUN.  This campaign adds
declarations to `YangMills/OS/SpatialOS.lean`, an EXISTING member of the core.
It adds NO module and touches no import.  The house convention (ledger, e.g.
the `RG/AnimalCount.lean` entry) is that a build job is a module, so the
prediction is EQUALITY: the count must come back UNCHANGED from the baseline
this run is started against.  A count that moved would mean the change was not
what it is described as, and stage 4 says so rather than accepting it.

Usage, from a fresh Colab clone:

    !python scripts/colab_sblock_runner.py <expected-sha> <baseline-jobs>
"""

import hashlib
import os
import re
import subprocess
import sys

REPO = "/content/eriksson"
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
EXPECTED_MATHLIB_PIN = "07642720480157414db592fa85b626dafb71355b"
LANE_MODULES = ["YangMills.OS.SpatialOS"]
CERTIFIERS = ["scripts/judge_site_bridge.py", "scripts/judge_spatial_os.py"]
TRAVELLING = [
    "YangMills/OS/SpatialOS.lean",
    "oracle_check.lean",
    "scripts/judge_site_bridge.py",
]
OUT = "/content/artefacts"

SENTINEL_ABSENT = "absent"
SENTINEL_MALFORMED = "malformed"
SENTINEL_NONZERO = "nonzero"
SENTINEL_ZERO = "zero"

JOBS = re.compile(r"\((\d+)\s+jobs?\)")


def write_sentinel(path, code):
    """Atomic, validated, one decimal line."""
    tmp = path + ".writing"
    with open(tmp, "w", encoding="ascii") as f:
        f.write("%d\n" % int(code))
        f.flush()
        os.fsync(f.fileno())
    with open(tmp, encoding="ascii") as f:
        body = f.read().strip()
    if not body or re.fullmatch(r"-?\d+", body) is None:
        os.remove(tmp)
        raise SystemExit("FATAL: refusing to publish a malformed sentinel for "
                         + path)
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
    log = os.path.join(OUT, "%s.%s.log" % (name, mode))
    sen = os.path.join(OUT, "%s.%s.sentinel" % (name, mode))
    print("  -> %s [%s] : %s" % (name, mode, " ".join(cmd)), flush=True)
    with open(log, "w", encoding="utf-8", errors="replace") as lf:
        p = subprocess.run(cmd, cwd=cwd, stdout=lf, stderr=subprocess.STDOUT,
                           env=env)
    write_sentinel(sen, p.returncode)
    state, code = read_sentinel(sen)
    print("     sentinel: %s (%s)   log: %s" % (state, code, log), flush=True)
    return state, code, log


def sha256_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


# ---------------------------------------------------------------- stage 0
def stage0(expected_sha):
    print("stage 0 - environment")
    sha = subprocess.run(["git", "rev-parse", "HEAD"], cwd=REPO,
                         capture_output=True, text=True).stdout.strip()
    tc = open(os.path.join(REPO, "lean-toolchain"), encoding="utf-8").read().strip()
    manifest = open(os.path.join(REPO, "lake-manifest.json"), encoding="utf-8").read()
    pin_ok = EXPECTED_MATHLIB_PIN in manifest

    print("  repo SHA        : %s" % sha)
    print("  toolchain       : %s" % tc)
    print("  mathlib pin     : %s" % ("found" if pin_ok else "NOT FOUND"))

    problems = []
    if expected_sha and sha != expected_sha:
        problems.append("repo SHA %s != expected %s" % (sha, expected_sha))
    if tc != EXPECTED_TOOLCHAIN:
        problems.append("toolchain %s != expected %s" % (tc, EXPECTED_TOOLCHAIN))
    if not pin_ok:
        problems.append("Mathlib pin %s absent from lake-manifest.json"
                        % EXPECTED_MATHLIB_PIN)
    if problems:
        for p in problems:
            print("  MISMATCH: %s" % p)
        raise SystemExit("FATAL stage 0 - refusing to compile against an "
                         "environment that is not the one this lane pinned")
    print("  stage 0 OK")
    return sha


# ---------------------------------------------------------------- stage 1
def stage1():
    """Certifiers in BOTH modes.  A gate that behaves differently under -O is a
    gate that can be deleted by a flag."""
    print("stage 1 - certifiers, normal and optimized")
    results = {}
    for script in CERTIFIERS:
        base = os.path.basename(script).replace(".py", "")
        for mode, argv in (("normal", [sys.executable, script]),
                           ("optimized", [sys.executable, "-O", script])):
            results[(base, mode)] = run(argv, base, mode)
    return results


# ---------------------------------------------------------------- stage 2/3
def stage2():
    print("stage 2 - Lean")
    out = {}
    for m in LANE_MODULES:
        out[m] = run(["lake", "build", m], m.replace(".", "_"), "normal")
    out["YangMillsCore"] = run(["lake", "build", "YangMillsCore"],
                               "YangMillsCore", "normal")
    return out


def stage3():
    print("stage 3 - oracle")
    return run(["lake", "env", "lean", "oracle_check.lean"], "oracle", "normal")


# ---------------------------------------------------------------- stage 4
def stage4(baseline):
    """The job count, against the prediction registered in this file's header.

    Not an `assert`: an explicit check with its own exit contribution, so that
    `python -O` cannot delete the one line that would notice the campaign was
    not the shape it claims.
    """
    print("stage 4 - job count against the pre-registered prediction")
    log = os.path.join(OUT, "YangMillsCore.normal.log")
    if not os.path.exists(log):
        print("  core build log absent - cannot read a job count")
        return SENTINEL_ABSENT, None, log
    text = open(log, encoding="utf-8", errors="replace").read()
    hits = JOBS.findall(text)
    if not hits:
        print("  NO job count in the core build log.  Not treated as a pass:")
        print("  the prediction was equality, and a count that cannot be read")
        print("  is an INCONCLUSIVE HARNESS, not a satisfied prediction.")
        return SENTINEL_MALFORMED, None, log
    jobs = int(hits[-1])
    print("  measured  : %d jobs" % jobs)
    print("  predicted : %s (no module added, no import touched)"
          % (baseline if baseline else "<no baseline given>"))
    if baseline is None:
        print("  NO BASELINE GIVEN - reported, not judged.")
        return SENTINEL_MALFORMED, jobs, log
    if jobs != baseline:
        print("  PREDICTION FAILED: the count moved by %+d.  The change is not"
              % (jobs - baseline))
        print("  the shape it is described as; do not accept it.")
        return SENTINEL_NONZERO, jobs, log
    print("  prediction held: unchanged.")
    return SENTINEL_ZERO, jobs, log


# ---------------------------------------------------------------- stage 5
def stage5(sha):
    print("stage 5 - hashes")
    rows = []
    for f in TRAVELLING:
        p = os.path.join(REPO, f)
        if os.path.exists(p):
            rows.append((f, sha256_file(p), os.path.getsize(p)))
    print("  repo SHA %s" % sha)
    for f, h, n in rows:
        print("  %s  %8d  %s" % (h, n, f))
    return rows


def summarise(all_results):
    print()
    print("=" * 74)
    bad = []
    checked = 0
    for key, value in all_results.items():
        state, code = value[0], value[1]
        tag = key if isinstance(key, str) else "%s [%s]" % (key[0], key[1])
        checked += 1
        print("  %-48s %s (%s)" % (tag, state, code))
        if state != SENTINEL_ZERO:
            bad.append(tag)
    print("=" * 74)
    print("children accounted for: %d" % checked)
    if bad:
        print("RUN VERDICT: FAIL - %d not zero: %s" % (len(bad), ", ".join(bad)))
        return 1
    print("RUN VERDICT: every child exited zero and the job-count prediction "
          "held.  This is a PASS CANDIDATE, not a PASS: the logs still have to "
          "be read.")
    return 0


def main():
    expected_sha = sys.argv[1] if len(sys.argv) > 1 else None
    baseline = int(sys.argv[2]) if len(sys.argv) > 2 else None
    sha = stage0(expected_sha)
    results = {}
    results.update(stage1())
    results.update(stage2())
    results["oracle"] = stage3()
    results["jobcount"] = stage4(baseline)
    stage5(sha)
    return summarise(results)


if __name__ == "__main__":
    sys.exit(main())
