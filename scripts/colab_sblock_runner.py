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

THE JOB-COUNT PREDICTION, REGISTERED BEFORE ANY COUNT IS MEASURED.

The campaign has two parts and they predict different things.  The SITE BRIDGE
adds declarations to `YangMills/OS/SpatialOS.lean`, an EXISTING member of the
core: no module, no import, and by the house convention that a build job is a
module (ledger, e.g. the `RG/AnimalCount.lean` and Addendum 574 entries) that
contributes ZERO.  The RECONSTRUCTION adds exactly ONE new module,
`YangMills/OS/SpatialReconstruction.lean`, imported once by `YangMillsCore`.

  v1.0 CAMPAIGN PREDICTION:  jobs(after) - jobs(before)  =  +1, exactly.
  v2   CAMPAIGN PREDICTION:  jobs(after) = 8469 and the delta = 0, exactly.

The v2 campaign adds declarations to EXISTING modules only: no module, no
import, so the count must not move from the v1.0 anchor's absolute.  Both halves
are checked, because the registration in commit `6e67629a` made both claims.

THE FIRST VERSION OF THIS FILE SHIPPED IN THE CLEAN ANCHOR STILL DEMANDING `+1`,
which would have REJECTED the very measurement the manuscript's filler must
accept.  A committed procedure that contradicts the committed prediction is
worse than no procedure: it looks like evidence.

THREE BASELINES, AND THEY ARE DIFFERENT NUMBERS.  An earlier version of this
paragraph named only the first and would have had `stage4` compare the v2
prediction against the wrong one:

    v1 original campaign parent 345479fa      -> 8468
    v1 PUBLISHED anchor c90dc745, = v2 base   -> 8469
    v2 candidate anchor                       -> expected 8469, delta 0

So `--before` for a v2 run is the v1.0 PUBLISHED anchor's count, not the
campaign parent's.  A copied count may not be used as a baseline, and this
runner receives `--before` as a bare integer, which it CANNOT verify came
from a build: the transcript must therefore carry the baseline build's
command, SHA and log alongside it.  That limitation is stated rather than
papered over.

WHICH BASE, AND THE MISTAKE THIS PARAGRAPH EXISTS TO PREVENT.  The first version
of this header named `6d71e51b` --- the MERGE-BASE WITH `main` --- as "this
campaign's base".  It is not.  This branch descends from the Dobrushin lane,
which had already added modules to the core, so the measured
`6d71e51b -> HEAD` delta came back `+4` (8465 -> 8469) and looked like a failed
prediction.  It was not: it was the wrong `before`.  Measured at the campaign's
real base `345479fa`, the parent of its first commit, the core is 8468 and the
delta is exactly `+1`, as predicted.

Both numbers are true and they answer different questions.  `+4` is
branch-versus-`main` and includes `+3` inherited from another lane; `+1` is this
campaign.  A prediction about a campaign must be tested against the campaign's
own parent commit, never against a merge-base --- and a number that disagrees is
first suspected of measuring the wrong thing, exactly as an inconclusive harness
is not a failed judge.

Usage, from a fresh Colab clone:

    !python scripts/colab_sblock_runner.py <expected-sha> <jobs-before-measured>
"""

import hashlib
import os
import re
import subprocess
import sys

# Overridable, so the runner can be pointed at the fresh clone actually used
# rather than at a path that happens to be the first one this lane ever wrote.
REPO = os.environ.get("ERIKSSON_REPO", "/content/eriksson")
OUT_DEFAULT = os.environ.get("ERIKSSON_OUT", "/content/artefacts")
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
EXPECTED_MATHLIB_PIN = "07642720480157414db592fa85b626dafb71355b"
LANE_MODULES = ["YangMills.OS.SpatialOS", "YangMills.OS.SpatialReconstruction"]
CERTIFIERS = ["scripts/judge_site_bridge.py",
              "scripts/judge_os_reconstruction.py",
              "scripts/judge_spatial_os.py"]
TRAVELLING = [
    "YangMills/OS/SpatialOS.lean",
    "YangMills/OS/SpatialReconstruction.lean",
    "oracle_check.lean",
    "scripts/judge_site_bridge.py",
]
OUT = OUT_DEFAULT

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
    dirty = subprocess.run(["git", "status", "--porcelain"], cwd=REPO,
                           capture_output=True, text=True).stdout.strip()
    tracked = [l for l in dirty.splitlines() if not l.startswith("??")]
    if tracked:
        for l in tracked:
            print("  DIRTY: %s" % l)
        raise SystemExit("FATAL stage 0 - a correct HEAD does not imply a "
                         "clean worktree, and this campaign has already been "
                         "bitten by a shared clone")
    print("  worktree clean (no modified tracked files)")
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
REGISTERED_JOBS_ABSOLUTE = 8469   # commit 6e67629a, before any v2 count
REGISTERED_JOBS_DELTA = 0


def stage2b():
    """Elaborate the two paper sources DIRECTLY.

    With warm `.lake` artefacts a green `lake build` cannot distinguish a
    module that was re-elaborated from one whose olean already matched.
    `lake env lean <file>` reads and elaborates the named file regardless.
    """
    print("stage 2b - direct source elaboration (warm artefacts cannot fake this)")
    out = {}
    for f in ("YangMills/OS/SpatialOS.lean",
              "YangMills/OS/SpatialReconstruction.lean"):
        out["elab:" + f] = run(["lake", "env", "lean", f],
                               os.path.basename(f).replace(".lean", "") + "_elab",
                               "normal")
    return out


def stage4(baseline):
    """The job count, against the prediction registered before any v2 count:
    the absolute is 8469 AND the delta is 0.

    Not an `assert`: an explicit check with its own exit contribution, so that
    `python -O` cannot delete the one line that would notice the campaign was
    not the shape it claims.
    """
    print("stage 4 - v2 job count: registered absolute %d and delta %+d"
          % (REGISTERED_JOBS_ABSOLUTE, REGISTERED_JOBS_DELTA))
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
    print("  measured after  : %d jobs" % jobs)
    if baseline is None:
        print("  NO MEASURED BASELINE GIVEN - reported, not judged.  A count")
        print("  copied from a document is not a baseline; see the header.")
        return SENTINEL_MALFORMED, jobs, log
    print("  measured before : %d jobs" % baseline)
    delta = jobs - baseline
    print("  delta           : %+d   (registered %+d at absolute %d)"
          % (delta, REGISTERED_JOBS_DELTA, REGISTERED_JOBS_ABSOLUTE))
    if jobs != REGISTERED_JOBS_ABSOLUTE:
        print("  PREDICTION FAILED: absolute %d is not the registered %d."
              % (jobs, REGISTERED_JOBS_ABSOLUTE))
        return SENTINEL_NONZERO, jobs, log
    if delta != REGISTERED_JOBS_DELTA:
        print("  PREDICTION FAILED: measured delta %+d, registered delta %+d."
              % (delta, REGISTERED_JOBS_DELTA))
        return SENTINEL_NONZERO, jobs, log
    print("  prediction held: the core stayed at %d and the delta is %+d."
          % (jobs, delta))
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
    print()
    print('PRE-BUILD HASHES (what is about to be elaborated)')
    pre_hashes = dict((f, h) for f, h, _n in stage5(sha))
    results = {}
    results[("prereg_blobs", "normal")] = run(
        [sys.executable, "scripts/verify_prereg_blobs.py", "HEAD"],
        "prereg_blobs", "normal")
    results[("prereg_blobs", "optimized")] = run(
        [sys.executable, "-O", "scripts/verify_prereg_blobs.py", "HEAD"],
        "prereg_blobs", "optimized")
    results[("lean_decls", "normal")] = run(
        [sys.executable, "scripts/lean_decls.py"],
        "lean_decls", "normal")
    results[("lean_decls", "optimized")] = run(
        [sys.executable, "-O", "scripts/lean_decls.py"],
        "lean_decls", "optimized")
    results.update(stage1())
    results.update(stage2b())
    results.update(stage2())
    results["oracle"] = stage3()
    results["jobcount"] = stage4(baseline)
    print()
    print('POST-BUILD HASHES (what was actually elaborated)')
    post_hashes = dict((f, h) for f, h, _n in stage5(sha))
    same = pre_hashes == post_hashes
    for f in sorted(set(pre_hashes) | set(post_hashes)):
        if pre_hashes.get(f) != post_hashes.get(f):
            print('  MUTATED DURING THE RUN: %s' % f)
    results['pre/post hashes identical'] = (
        SENTINEL_ZERO if same else SENTINEL_NONZERO,
        0 if same else 1, 'in-memory comparison')
    return summarise(results)


if __name__ == "__main__":
    sys.exit(main())
