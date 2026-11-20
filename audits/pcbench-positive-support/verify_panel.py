from pathlib import Path
import json,sys,subprocess,hashlib
root=Path(__file__).parent
source=json.loads((root/'source.json').read_bytes())
for name,digest in source['table_sha256'].items():
    if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:raise ValueError('Source table differs')
got=json.loads(subprocess.check_output([sys.executable]+(['-O'] if sys.flags.optimize else [])+['panel_identify.py'],cwd=root))
if got!=json.loads((root/'panel-identification.json').read_bytes()):raise ValueError('Row certificate differs')
print(json.dumps(got['crosstab'],sort_keys=True))
