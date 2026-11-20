"""Reproduce the deterministic certificates from the released tables."""
import json,subprocess,sys
from pathlib import Path
root=Path(__file__).parent
for script,reference in [('qc_frontier.py','frontier.json'),('qc_windows.py','windows.json')]:
    actual=json.loads(subprocess.check_output([sys.executable,script],cwd=root))
    if actual!=json.loads((root/reference).read_bytes()):raise ValueError(script)
print('Verified all month pair and joint allocation certificates')