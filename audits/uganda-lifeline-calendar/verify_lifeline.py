from pathlib import Path
import json,subprocess,sys,zipfile,hashlib
def need(ok):
    if not ok:raise ValueError('Invalid tariff certificate')
def main():
    manifest=json.loads(Path('load-sources.json').read_bytes())
    with zipfile.ZipFile('source.zip') as z:
        need(len(z.namelist())==len(manifest) and set(z.namelist())==set(manifest))
        for name,digest in manifest.items():need(hashlib.sha256(z.read(name)).hexdigest()==digest)
    for f,r in [('uganda-quarter.py','calendar.json'),('uganda-order.py','order.json')]:
        data=json.loads(subprocess.check_output([sys.executable,f]));need(data==json.loads(Path(r).read_bytes()))
    a=json.loads(Path('calendar.json').read_bytes());b=json.loads(Path('order.json').read_bytes())
    need(sum(b['by_spread_in_discount_months'].values())==b['groups'] and a['matched_groups']==sum(b['six_high_groups'].values()))
    print(json.dumps(dict(groups=b['groups'],maxima=b['max_months_by_high_count'],fixed_six=a['maximum_spread_UGX']),sort_keys=True))
if __name__=='__main__':main()