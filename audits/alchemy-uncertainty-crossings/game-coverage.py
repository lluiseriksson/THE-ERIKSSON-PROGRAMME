"""Count actual S4 rows and players covered by uncertainty-slope certificates."""
import hashlib,json,tempfile
from pathlib import Path
import numpy as np
import pandas as pd
import requests

def run():
    case=json.loads(Path('spec.json').read_bytes())
    src=case['source']
    with tempfile.TemporaryDirectory() as d:
        path=Path(d)/'input.csv';digest=hashlib.sha256()
        with requests.get(src['url'],params={'p':src['path'],'dl':'1'},stream=True,timeout=(15,70)) as r, path.open('wb') as f:
            r.raise_for_status()
            for chunk in r.iter_content(4*1024*1024):
                f.write(chunk);digest.update(chunk)
        if digest.hexdigest()!=src['sha256'] or path.stat().st_size!=src['size']:raise ValueError('Source integrity')
        table=pd.read_csv(path,usecols=['id','trial','first','second'],dtype=np.int32)
    table=table.sort_values(['id','trial'],kind='stable',ignore_index=True)
    first=~table.duplicated(['id','first','second'])
    progress=first.groupby(table.id,sort=False).cumsum()-1
    if table.duplicated(['id','trial']).any():raise ValueError('Tied trial within player')
    counts=[int(len(table)),int(first.sum()),int((~first).sum()),int(table.id.nunique())]
    if counts!=[6212596,4691033,1521563,29493]:raise ValueError(('Paper mismatch',counts))
    results={}
    for name,spans in case['regions'].items():
        mask=np.zeros(len(table),dtype=bool)
        for lo,hi in spans:mask|=progress.between(lo,hi).to_numpy()
        def coverage(selected):
            a=table.id[mask & selected];tot=table.id[selected]
            return {'covered_rows':int(a.size),'rows_total':int(tot.size),'players_covered':int(a.nunique()),'players_in_subset':int(tot.nunique())}
        fids=set(table.id[mask & first]);rids=set(table.id[mask & ~first])
        results[name]=dict(first=coverage(first),repeat=coverage(~first),players_with_both=len(fids&rids))
    return dict(source_sha256=src['sha256'],regions=case['regions'],coverage=results,totals=counts)
if __name__=='__main__':print(json.dumps(run(),sort_keys=True))
