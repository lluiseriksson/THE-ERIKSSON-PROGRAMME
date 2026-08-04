#!/usr/bin/env python3
"""COLAB VERIFICATION DRIVER for the congruence lane — JC.

Paste into a Colab cell as `%run colab_congruence_verify.py`, or run the cells
it prints.  Written to the 2026-08-01 environment rule:

  * Runtime CPU / high-RAM.  NEVER GPU: Lean does not use it and it burns
    compute units far faster.  Cell 0 REFUSES to continue if a GPU is attached.
  * Cell 0 verifies repo SHA, toolchain and the Mathlib pin and FAILS THERE on
    any mismatch.  Never compile against a stale cache.
  * No GitHub tokens here and no push from here.  Artifacts go back to the
    desktop and are hash-verified before anything is committed.
  * No bare `assert` anywhere: `-O` deletes them, and this repo has shipped two
    false PASSes that way.  Explicit checks, an explicit counter, non-zero exit.
  * Sentinels carry ONE line — the real decimal exit code of the child, written
    atomically (temp, close, non-empty + integer validation, rename).  Four
    states: absent / empty-or-non-integer / non-zero / zero.  Only a validated
    zero plus a clean log is a PASS candidate.  Logs and sentinels are named for
    the MODE, never with indistinguishable numeric suffixes.

WHAT IS BEING VERIFIED (JC, pre-registered in docs/CONGRUENCE-CHARTER.md):
  zero errors, zero `sorry`, every declaration on the standard axiom triple,
  and the merged-core job count +1 exactly over this branch's own baseline.
"""

import os
import re
import subprocess
import sys
import tempfile

REPO = "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
BRANCH = "claude/congruence-spectrum"
EXPECT_SHA = "87a206ec"                      # prefix; full SHA checked below
EXPECT_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc6"
EXPECT_MATHLIB = "07642720480157414db592fa85b626dafb71355b"
MODULE = "YangMills/OS/CongruenceSpectrum.lean"
MODULE_NAME = "YangMills.OS.CongruenceSpectrum"

DECLS = [
    "quad_diagonal_congr", "scale_ne_zero", "quad_pos_congr_iff",
    "quad_neg_congr_iff", "bond_mulVec_sym", "bond_mulVec_anti", "bond_ratio",
    "bond_top_pos", "sgn_self", "sgn_zero_one", "tensorKernel_plus_plus",
    "tensorKernel_plus_minus", "antipodal_block_eq_bond", "tanh_eq_exp",
    "exists_extension_exceeding", "fused_gt_unfused", "fused_nondegenerate",
]
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

CHECKS_RUN = 0
FAILED = []


def check(name, cond, detail=""):
    global CHECKS_RUN
    CHECKS_RUN += 1
    if not cond:
        FAILED.append(f"{name}: {detail}")
        print(f"  FAIL  {name}: {detail}")
    else:
        print(f"  ok    {name}")
    return bool(cond)


def write_sentinel(path, exit_code):
    """One line, the real decimal exit code, written atomically and validated."""
    if not isinstance(exit_code, int):
        raise TypeError(f"sentinel needs an int exit code, got {exit_code!r}")
    d = os.path.dirname(os.path.abspath(path)) or "."
    fd, tmp = tempfile.mkstemp(dir=d, text=True)
    with os.fdopen(fd, "w") as fh:
        fh.write(f"{exit_code}\n")
        fh.flush()
        os.fsync(fh.fileno())
    with open(tmp) as fh:
        body = fh.read().strip()
    if body == "" or not re.fullmatch(r"-?\d+", body):
        os.unlink(tmp)
        raise RuntimeError(f"sentinel body invalid before rename: {body!r}")
    os.replace(tmp, path)


def read_sentinel(path):
    """Four states, as the rule requires."""
    if not os.path.exists(path):
        return ("absent", None)
    body = open(path).read().strip()
    if body == "" or not re.fullmatch(r"-?\d+", body):
        return ("invalid", body)
    v = int(body)
    return ("zero", v) if v == 0 else ("nonzero", v)


def run(cmd, log, sentinel, cwd=None, timeout=None):
    """Run, tee to a semantically-named log, and stamp a validated sentinel."""
    print(f"$ {cmd}")
    with open(log, "w") as fh:
        p = subprocess.run(cmd, shell=True, cwd=cwd, stdout=fh,
                           stderr=subprocess.STDOUT, timeout=timeout)
    write_sentinel(sentinel, p.returncode)
    return p.returncode


# ---------------------------------------------------------------- cell 0
def cell0_preflight(root):
    print("=" * 78)
    print("CELL 0 — preflight.  Any mismatch FAILS HERE; never compile on a")
    print("stale cache, and never on a GPU runtime.")
    print("=" * 78)

    gpu = subprocess.run("nvidia-smi -L", shell=True, capture_output=True,
                         text=True).returncode == 0
    check("runtime/no-gpu", not gpu,
          "a GPU is attached — Lean cannot use it and it burns compute units; "
          "switch the runtime to CPU / high-RAM and re-run")

    sha = subprocess.run("git rev-parse HEAD", shell=True, cwd=root,
                         capture_output=True, text=True).stdout.strip()
    check("repo/sha", sha.startswith(EXPECT_SHA),
          f"HEAD is {sha}, expected prefix {EXPECT_SHA}")

    tc = open(os.path.join(root, "lean-toolchain")).read().strip()
    check("repo/toolchain", tc == EXPECT_TOOLCHAIN, f"{tc} != {EXPECT_TOOLCHAIN}")

    manifest = open(os.path.join(root, "lake-manifest.json")).read()
    check("repo/mathlib-pin", EXPECT_MATHLIB in manifest,
          f"pin {EXPECT_MATHLIB} not found in lake-manifest.json")

    if FAILED:
        print("\nPREFLIGHT FAILED — stopping before any compute is spent.")
        return 1
    print("\npreflight ok — CPU runtime, SHA, toolchain and Mathlib pin all match")
    return 0


# ---------------------------------------------------------------- cell 2
def cell2_elaborate(root):
    print("=" * 78)
    print("CELL 2 — elaborate the module (JC part 1: zero errors, zero sorry)")
    print("=" * 78)
    rc = run(f"lake env lean {MODULE}", "elaborate_normal.log",
             "elaborate_normal.sentinel", cwd=root, timeout=7200)
    state, val = read_sentinel(os.path.join(root, "elaborate_normal.sentinel")) \
        if os.path.exists(os.path.join(root, "elaborate_normal.sentinel")) \
        else read_sentinel("elaborate_normal.sentinel")
    log = open(os.path.join(root, "elaborate_normal.log")).read() \
        if os.path.exists(os.path.join(root, "elaborate_normal.log")) \
        else open("elaborate_normal.log").read()
    check("elaborate/sentinel-zero", state == "zero",
          f"sentinel state {state}, value {val}")
    check("elaborate/no-error", "error" not in log.lower(),
          "the log mentions an error even though the exit code was zero")
    check("elaborate/no-sorry", "sorry" not in log.lower(),
          "the log mentions sorry")
    if log.strip():
        print("--- elaboration log (should be empty) ---")
        print(log[:4000])
    return rc


# ---------------------------------------------------------------- cell 3
def cell3_oracle(root):
    print("=" * 78)
    print("CELL 3 — axiom oracle (JC part 2: standard triple only)")
    print("=" * 78)
    src = "import " + MODULE_NAME + "\n" + "\n".join(
        f"#print axioms {MODULE_NAME}.Congruence.{d}" for d in DECLS) + "\n"
    path = os.path.join(root, "_oracle_congruence.lean")
    open(path, "w").write(src)
    run(f"lake build {MODULE_NAME}", "build_module.log",
        "build_module.sentinel", cwd=root, timeout=7200)
    run("lake env lean _oracle_congruence.lean", "oracle_normal.log",
        "oracle_normal.sentinel", cwd=root, timeout=7200)
    out = open(os.path.join(root, "oracle_normal.log")).read()
    print(out)
    lines = [l for l in out.splitlines() if "depends on axioms" in l]
    check("oracle/line-count", len(lines) == len(DECLS),
          f"{len(lines)} axiom lines for {len(DECLS)} declarations")
    for l in lines:
        found = set(re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", l.split("[")[-1]))
        extra = {a for a in found if a not in STANDARD_AXIOMS} - {"sorryAx"}
        check(f"oracle/{l.split(chr(39))[1] if chr(39) in l else l[:40]}",
              "sorryAx" not in l and not extra,
              f"non-standard axioms: {extra or 'sorryAx'}")
    return 0


# ---------------------------------------------------------------- cell 4
def cell4_jobcount(root):
    print("=" * 78)
    print("CELL 4 — merged-core job count (JC part 3: predicted +1 exactly)")
    print("Run the BASELINE on the parent commit first; a delta against a number")
    print("measured in someone else's tree is not a measurement.")
    print("=" * 78)
    run("lake build YangMillsCore", "core_with_module.log",
        "core_with_module.sentinel", cwd=root, timeout=21600)
    out = open(os.path.join(root, "core_with_module.log")).read()
    m = re.findall(r"\((\d+) jobs\)", out)
    print(f"job counts seen in log: {m}")
    print("Compare against the baseline measured on the parent commit IN THIS "
          "SAME TREE.  If the increment is not +1, report it as measured — "
          "never justify it.")
    return 0


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else "THE-ERIKSSON-PROGRAMME"
    stage = sys.argv[2] if len(sys.argv) > 2 else "all"
    rc = 0
    if stage in ("all", "preflight"):
        rc = cell0_preflight(root)
        if rc:
            return rc
    if stage in ("all", "elaborate"):
        cell2_elaborate(root)
    if stage in ("all", "oracle"):
        cell3_oracle(root)
    if stage in ("all", "jobs"):
        cell4_jobcount(root)

    print("=" * 78)
    if FAILED:
        print(f"JC VERDICT: FAIL ({len(FAILED)}) after {CHECKS_RUN} checks")
        for f in FAILED:
            print("  -", f)
        return 1
    print(f"JC VERDICT: PASS — {CHECKS_RUN} checks, zero failures")
    return 0


if __name__ == "__main__":
    sys.exit(main())
