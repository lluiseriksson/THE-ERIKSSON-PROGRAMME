"""Validate archived source replies and reproduce the complete empirical certificate."""
from pathlib import Path
import hashlib,json,subprocess,sys,tempfile,zipfile
from fractions import Fraction as Q
from tide_coverage import extremes
def need(x):
    if not x:raise ValueError('Certificate mismatch')
def main():
    root=Path(__file__).resolve().parent
    manifest=json.loads((root/'noaa-manifest.json').read_bytes())
    with tempfile.TemporaryDirectory() as td:
        d=Path(td)
        with zipfile.ZipFile(root/'noaa-inputs.zip') as z:
            need(set(z.namelist())==set(manifest) and len(z.namelist())==len(manifest))
            for name,entry in manifest.items():
                raw=z.read(name);need(Path(name).name==name and hashlib.sha256(raw).hexdigest()==entry['sha256'])
                (d/name).write_bytes(raw)
        (d/'noaa-manifest.json').write_bytes((root/'noaa-manifest.json').read_bytes())
        v=json.loads(subprocess.check_output([sys.executable,str(root/'tide_coverage.py')],cwd=d))
    need(v==json.loads((root/'tides.json').read_bytes()))
    for m,row in v['months'].items():
        stats=[tuple(map(Q,row['stations'][n]['moments'])) for n in row['weight_order']]
        for target,bracket in row['thresholds'].items():
            n=bracket['first_passing'];t=Q(target)
            need(bracket['last_failing']==n-1 and extremes(stats,Q(n-1,10000))[0][0]<t*t<=extremes(stats,Q(n,10000))[0][0])
    print(json.dumps({m:r['thresholds'] for m,r in v['months'].items()},sort_keys=True))
if __name__=='__main__':main()