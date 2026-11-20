"""Verify the retained design witnesses against their frozen outputs."""
from pathlib import Path
import json, subprocess,sys
def read(name):
    return json.loads(Path(name).read_bytes())
for script, saved in [('systematic-zero.py','zero.json'),('paired-phase.py','paired-phase.json'),('missing-phase.py','missing-phase.json')]:
    answer=json.loads(subprocess.check_output([sys.executable,script]))
    if answer!=read(saved):raise ValueError(saved)
missing=read('missing-phase.json')
if missing['worst']!=2 or missing['checked']!=62559 or missing['number_of_offsets_checked']!=127:raise ValueError('missing-label certificate')
print(json.dumps(dict(all_witnesses_match=True,placements=62559,offsets=127)))