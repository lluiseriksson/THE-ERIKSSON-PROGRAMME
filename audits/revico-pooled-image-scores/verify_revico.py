from pathlib import Path
import json,subprocess,sys
for script,target in [('revico_audit.py','audit.json'),('revico_counts.py','counts.json'),('language_verify.py','language.json')]:
    cmd=[sys.executable]+(['-O'] if sys.flags.optimize else [])+[script]
    value=json.loads(subprocess.check_output(cmd))
    if value!=json.loads(Path(target).read_bytes()):raise ValueError('Mismatch: '+target)
print(json.dumps(dict(vision_models=20,prompt_rows=24,denominators_tested=1229,language_rows=20)))
