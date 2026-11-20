import json,subprocess,sys
from pathlib import Path
from robust_water import scenarios,groups,replay
from water_ranges import replay as range_replay
signed=json.loads(subprocess.check_output([sys.executable,'nanpan_alignment_signed.py']))
if signed!=json.loads(Path('signed.json').read_bytes()):raise ValueError('Signed inputs differ from CSV')
a=json.loads(Path('robust.json').read_bytes());d=dict(groups(scenarios()))
if a.keys()!=d.keys():raise ValueError('Missing information group')
bounds={group:replay(rows,a[group]) for group,rows in d.items()}
v=json.loads(Path('ranges.json').read_bytes())
actual=range_replay(v)
if json.loads(json.dumps(actual))!=v['bounds']:raise ValueError('Coordinate projections differ')
print(json.dumps({'scenarios':len(scenarios()),'costs':bounds,'marginal_ranges':actual},sort_keys=True))