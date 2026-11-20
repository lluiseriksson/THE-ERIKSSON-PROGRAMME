import json, subprocess, sys
from pathlib import Path
root=Path(__file__).parent
for script, filename in [('context_cut.py','cut-witnesses.json'),('rank_budget.py','aggregate-witnesses.json')]:
    result=json.loads(subprocess.check_output([sys.executable,script],cwd=root))
    if result!=json.loads((root/filename).read_bytes()):
        raise ValueError('Incorrect certificate: '+script)
print('Verified single-ranking and aggregate-ranking certificates')