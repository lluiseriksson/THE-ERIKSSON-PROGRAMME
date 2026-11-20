from pathlib import Path
import sys,subprocess,json
got=json.loads(subprocess.check_output([sys.executable]+(['-O'] if sys.flags.optimize else [])+['metering_certify.py']))
if got!=json.loads(Path('car-cert.json').read_bytes()):raise ValueError('Exposure certificate differs')
print(json.dumps({'joint_tv':got['joint']['0']['tv']['radius'],'joint_maxnorm':got['joint']['0']['maxnorm']['radius'],'models':list(got['specs'])},sort_keys=True))
