import os
import subprocess
import time

repo = "/content/hrpoly-cmp89-flat-generated-finite-depth-reflection-cold"
sha = "6386220b842f55c52d1efea0ed35e9c5fc175688"
env = os.environ.copy()


def run(stage, cmd):
    print("STAGE=" + stage, flush=True)
    started = time.perf_counter()
    proc = subprocess.run(
        cmd,
        cwd=repo,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    print(proc.stdout, end="")
    print(
        "STAGE={} EXIT={} SECONDS={:.3f}".format(
            stage, proc.returncode, time.perf_counter() - started
        ),
        flush=True,
    )
    if proc.returncode != 0:
        raise RuntimeError("FIRST_ERROR=" + stage)


run("fetch", ["git", "fetch", "--no-tags", "origin", sha])
run("checkout", ["git", "checkout", "--detach", sha])
run("head", ["git", "rev-parse", "HEAD"])
run(
    "rectangle_region_focal",
    ["lake", "build", "YangMills.RG.BalabanCMP89NeumannRectangleActiveRegion"],
)
run(
    "rectangle_region_audit",
    [
        "lake",
        "env",
        "lean",
        "YangMills/RG/BalabanCMP89NeumannRectangleActiveRegionAudit.lean",
    ],
)
print("HOT_FINAL_STATUS=PASS", flush=True)
