"""Hot Colab diagnostic for the CMP89 mass-uniform full-G chain.

This deliberately reuses the retained project build graph.  It is not cold
evidence and must never remove PRE-VALIDATION notices or move counters.
"""

from pathlib import Path
import os
import subprocess
import time


SOURCE_SHA = "d773e70906ae74620b5f3ce2218e0f736541a60c"
REPO = Path("/content/hrpoly-cmp89-eq246-dictionary-reflection-cold-v1")
TARGETS = (
    "YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenCoefficientDictionary",
    "YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenCoefficientDictionaryAudit",
    "YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenFourierSummability",
    "YangMills.RG.BalabanCMP89Eq246MassUniformCenteredGreenFourierSummabilityAudit",
    "YangMills.RG.BalabanCMP99FullGreenFiniteGridAliasing",
    "YangMills.RG.BalabanCMP99FullGreenFiniteGridAliasingAudit",
)


env = os.environ.copy()
env["PATH"] = "/content/lean-4.29.0-rc6-linux/bin:" + env.get("PATH", "")


def run(command: list[str], stage: str) -> int:
    print(f"STAGE_BEGIN={stage}", flush=True)
    started = time.perf_counter()
    process = subprocess.Popen(
        command,
        cwd=REPO,
        env=env,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    assert process.stdout is not None
    for line in process.stdout:
        print(line, end="", flush=True)
    exit_code = process.wait()
    elapsed = time.perf_counter() - started
    print(
        f"STAGE_END={stage} EXIT={exit_code} SECONDS={elapsed:.3f}",
        flush=True,
    )
    return exit_code


print("MODE=HOT_DEBUG_NOT_EVIDENCE", flush=True)
print(f"SOURCE_SHA={SOURCE_SHA}", flush=True)
assert REPO.is_dir(), REPO

for command, stage in (
    (["git", "status", "--porcelain"], "pre_status"),
    (
        [
            "git",
            "fetch",
            "https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git",
            SOURCE_SHA,
        ],
        "fetch",
    ),
    (["git", "checkout", "--detach", SOURCE_SHA], "checkout"),
    (["git", "rev-parse", "HEAD"], "verify_head"),
):
    if run(command, stage) != 0:
        raise SystemExit(1)

head = subprocess.check_output(
    ["git", "rev-parse", "HEAD"], cwd=REPO, text=True
).strip()
assert head == SOURCE_SHA, (head, SOURCE_SHA)

for target in TARGETS:
    if run(["lake", "build", target], target) != 0:
        print("HOT_DEBUG_STATUS=FAIL", flush=True)
        raise SystemExit(1)

print("HOT_DEBUG_STATUS=PASS", flush=True)
