import subprocess, sys, os
from pathlib import Path

for pkg in ["gitpython"]:
    subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", pkg])

from git import Repo
from google.colab import userdata

TOKEN    = userdata.get("GITHUB_TOKEN")
REPO_URL = f"https://x-access-token:{TOKEN}@github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git"
CLONE_DIR = Path("/content/THE-ERIKSSON-PROGRAMME")

if CLONE_DIR.exists():
    repo = Repo(CLONE_DIR); repo.remotes.origin.pull()
else:
    repo = Repo.clone_from(REPO_URL, CLONE_DIR, branch="main")

ELAN_BIN = Path.home() / ".elan" / "bin"
os.environ["PATH"] = str(ELAN_BIN) + ":" + os.environ.get("PATH", "")

targets = [
    "YangMills.P8_PhysicalGap.RicciSU2Explicit",
    "YangMills.P8_PhysicalGap.RicciSUN",
    "YangMills.P8_PhysicalGap.StroockZegarlinski",
    "YangMills.P8_PhysicalGap.FeynmanKacBridge",
    "YangMills.P8_PhysicalGap.BalabanToLSI",
    "YangMills.P8_PhysicalGap.PhysicalMassGap",
    "YangMills.ErikssonBridge",
]

for target in targets:
    r = subprocess.run(
        [str(ELAN_BIN / "lake"), "build", target],
        cwd=CLONE_DIR, text=True, capture_output=True, timeout=300
    )
    errors = [l for l in (r.stdout+r.stderr).split("\n") if "error:" in l]
    sorrys = [l for l in (r.stdout+r.stderr).split("\n") if "sorry" in l.lower()]
    status = "✅" if r.returncode == 0 else "❌"
    print(f"{status} {target.split('.')[-1]}")
    if errors:
        for e in errors[:3]: print(f"    {e}")
    if r.returncode == 0 and not errors:
        print(f"   0 errors")
