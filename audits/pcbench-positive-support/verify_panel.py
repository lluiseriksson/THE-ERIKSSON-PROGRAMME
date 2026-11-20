from pathlib import Path
import json,sys,subprocess,hashlib
root=Path(__file__).parent
source=json.loads((root/'source.json').read_bytes())
for name,digest in source['table_sha256'].items():
    if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:raise ValueError('Source table differs')
got=json.loads(subprocess.check_output([sys.executable]+(['-O'] if sys.flags.optimize else [])+['panel_identify.py'],cwd=root))
if got!=json.loads((root/'panel-identification.json').read_bytes()):raise ValueError('Row certificate differs')
print(json.dumps(got['crosstab'],sort_keys=True))

for script,reference in [('panel_family.py','panel-family.json'),('proxy_bounds.py','proxy-median.json'),('proxy_overlap.py','proxy-overlap.json')]:
    result=json.loads(subprocess.check_output([sys.executable]+(['-O'] if sys.flags.optimize else [])+[script],cwd=root))
    if result!=json.loads((root/reference).read_bytes()):raise ValueError('Mismatch: '+script)
