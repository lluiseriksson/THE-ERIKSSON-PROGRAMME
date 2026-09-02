"""Retained-runtime diagnostic for the full-G endpoint-character dictionaries.

This deliberately reuses the cold final-aliasing build graph.  It is hot
diagnostic output, not sealing evidence: it must not retire PRE-VALIDATION or
move any counter.
"""

from pathlib import Path
import os
import re
import subprocess
import time


SOURCE_SHA = "973dc76539d7c872813542fab0bb652b94ed819b"
REPO = Path("/content/hrpoly-cmp89-mass-uniform-final-aliasing-cold-v1")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

QUEUE = (
    (
        "linearity",
        "YangMills.RG.BalabanCMP89Eq246StabilizedAliasTransposeFullSolutionLinearity",
        "YangMills/RG/BalabanCMP89Eq246StabilizedAliasTransposeFullSolutionLinearityAudit.lean",
        {
            "YangMills.RG.cmp89Eq246StabilizedAliasTransposeNoncentralSourceMoment_mul_right",
            "YangMills.RG.cmp89Eq246StabilizedAliasTransposeFullSolutionMoment_mul_right",
            "YangMills.RG.cmp89Eq246StabilizedAliasTransposeFullSolution_mul_right",
        },
    ),
    (
        "source_character",
        "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceCharacterDictionary",
        "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceCharacterDictionaryAudit.lean",
        {
            "YangMills.RG.cmp99FlatFourierMode_inv_eq_finePointSourceAliasVector_mul_coarseMode_inv",
            "YangMills.RG.cmp99FlatFourierMode_inv_eq_owned_finePointSourceAliasVector_mul_coarseMode_inv",
            "YangMills.RG.cmp89Eq246FinePointSourceAliasVector_comp_reflection_eq_neg",
            "YangMills.RG.cmp99SourceFlatFullComplexPrecisionPointSourceFibreCoefficients_apply_eq",
        },
    ),
    (
        "target_character",
        "YangMills.RG.BalabanCMP99SourceFlatFullPointSourceTargetCharacterDictionary",
        "YangMills/RG/BalabanCMP99SourceFlatFullPointSourceTargetCharacterDictionaryAudit.lean",
        {
            "YangMills.RG.cmp99FlatFourierMode_eq_fineTargetAliasPhase_mul_coarseMode",
            "YangMills.RG.cmp99FlatFourierMode_eq_owned_fineTargetAliasPhase_mul_coarseMode",
        },
    ),
)

# The first pair already passed in the preceding retained-runtime attempt.
# Resume stop-on-first-error at the repaired source-character focal.
QUEUE = QUEUE[1:]

env = os.environ.copy()
env["PATH"] = "/content/lean-4.29.0-rc6-linux/bin:" + env.get("PATH", "")


def run(command: list[str], stage: str) -> tuple[int, str]:
    print(f"STAGE_BEGIN={stage}", flush=True)
    started = time.perf_counter()
    child = subprocess.run(
        command,
        cwd=REPO,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    print(child.stdout, end="", flush=True)
    elapsed = time.perf_counter() - started
    print(f"STAGE_END={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}", flush=True)
    return child.returncode, child.stdout


def audit_gate(output: str, expected: set[str]) -> None:
    compact = re.sub(r"\s+", "", output)
    for forbidden in ("sorryAx", "ofReduceBool", "Lean.ofReduceBool"):
        if forbidden in compact:
            raise RuntimeError("FORBIDDEN_AXIOM=" + forbidden)
    with_axioms = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    without_axioms = re.findall(r"'([^']+)'doesnotdependonanyaxioms", compact)
    names = {name for name, _ in with_axioms} | set(without_axioms)
    if len(with_axioms) + len(without_axioms) != len(expected):
        raise RuntimeError("AXIOM_BLOCK_COUNT_MISMATCH=" + repr((with_axioms, without_axioms)))
    if names != expected:
        raise RuntimeError("AXIOM_DECLARATION_MISMATCH=" + repr(sorted(names)))
    for name, raw in with_axioms:
        axioms = {item for item in raw.split(",") if item}
        if not axioms.issubset(ALLOWED_AXIOMS):
            raise RuntimeError("AXIOM_SET=" + name + ":" + repr(sorted(axioms)))
        print("AXIOM_GATE=" + name + " AXIOMS=" + ",".join(sorted(axioms)), flush=True)
    for name in without_axioms:
        print("AXIOM_GATE=" + name + " AXIOMS=", flush=True)


print("MODE=HOT_DEBUG_NOT_EVIDENCE", flush=True)
print("SOURCE_SHA=" + SOURCE_SHA, flush=True)
assert REPO.is_dir(), REPO

for command, stage in (
    (["git", "status", "--porcelain"], "pre_status"),
    (["git", "fetch", "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git", SOURCE_SHA], "fetch"),
    (["git", "checkout", "--detach", SOURCE_SHA], "checkout"),
    (["git", "rev-parse", "HEAD"], "verify_head"),
):
    exit_code, _ = run(command, stage)
    if exit_code != 0:
        print("HOT_DEBUG_STATUS=FAIL", flush=True)
        raise SystemExit(1)

head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=REPO, text=True).strip()
if head != SOURCE_SHA:
    raise RuntimeError("SOURCE_SHA_MISMATCH=" + head)

for key, focal, audit, expected in QUEUE:
    exit_code, _ = run(["lake", "build", focal], key + "_focal")
    if exit_code != 0:
        print("HOT_DEBUG_STATUS=FAIL", flush=True)
        raise SystemExit(1)
    exit_code, output = run(["lake", "env", "lean", audit], key + "_audit")
    if exit_code != 0:
        print("HOT_DEBUG_STATUS=FAIL", flush=True)
        raise SystemExit(1)
    audit_gate(output, expected)

print("HOT_DEBUG_STATUS=PASS", flush=True)
