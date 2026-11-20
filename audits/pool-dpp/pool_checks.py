"""Run the four companion checks with the caller's optimization mode."""
import json
from pathlib import Path
import subprocess
import sys

def main():
    root = Path(__file__).resolve().parent
    checks = {}
    flags = ["-O"] if sys.flags.optimize else []
    for name in ("pool_marginal.py", "balanced_triples.py", "support/pair_balanced_support.py", "hesse.py"):
        output = subprocess.check_output([sys.executable, *flags, str(root/name)], cwd=root)
        checks[name] = json.loads(output)
    print(json.dumps(checks, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()

