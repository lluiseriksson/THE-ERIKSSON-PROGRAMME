"""Check the treatment identities, yield summaries and price thresholds in the public supplement."""
from decimal import Decimal
from fractions import Fraction as F
from pathlib import Path
from itertools import permutations
from statistics import mean
import hashlib, io, json, sys, zipfile
import xml.etree.ElementTree as ET

URL = 'https://mdpi-res.com/d_attachment/horticulturae/horticulturae-12-01452/article_deploy/horticulturae-12-01452-s001.zip'
DIGEST = '999ea8cd9363bd4030e5fafad23dcee05c1b5e5eebcfe33ee23c6c35038c5931'
LABELS = ('CK','T1','T2','T3','T4','T5')

def require(ok, why):
    if not ok:
        raise ValueError(why)

def cells(raw):
    require(hashlib.sha256(raw).hexdigest()==DIGEST, 'Supplement identity differs')
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        book=archive.read('horticulturae-4643263-supplementary.xlsx')
    with zipfile.ZipFile(io.BytesIO(book)) as sheet:
        strings=[''.join(node.itertext()) for node in ET.fromstring(sheet.read('xl/sharedStrings.xml'))]
        names=ET.fromstring(sheet.read('xl/workbook.xml')).findall('.//{*}sheet')
        require(names[1].get('name')=='Fruit yield and quality','Wrong worksheet')
        tree=ET.fromstring(sheet.read('xl/worksheets/sheet2.xml'))
        return {c.get('r'):(strings[int(v.text)] if c.get('t')=='s' else v.text)
                for c in tree.findall('.//{*}c') if (v:=c.find('{*}v')) is not None}

def cent(text):
    x=Decimal(text)
    y=x.quantize(Decimal('.01'))
    require(abs(x-y)<Decimal('0.000000001'),'Unexpected numerical precision')
    return F(y)

def film(y):
    return [y[j+1]-y[j] for j in (0,2,4)]

def interaction(groups):
    averages=[mean(a) for a in groups]
    gaps=film(averages)
    residual=sum(sum((v-m)**2 for v in a) for a,m in zip(groups,averages))
    f=(F(3,4)*sum((g-mean(gaps))**2 for g in gaps))/(residual/12)
    return {'F':str(f),'p':float((1+f/6)**-6)}

def audit(raw):
    c=cells(raw)
    require('Yield' in c['B55'] and c['D59']=='Mean' and c['D60']=='Standard Deviation','Labels changed')
    out={}
    for year,columns in [('2024','EFGHIJ'),('2025','LMNOPQ')]:
        require(year in c[columns[0]+'3'] and tuple(c[k+'55'] for k in columns)==LABELS,'Wrong year or order')
        groups=[[cent(c[k+str(i)]) for i in (56,57,58)] for k in columns]
        actual=[mean(group) for group in groups]
        reported=[cent(c[k+'59']) for k in columns]
        sds=[cent(c[k+'60']) for k in columns]
        var=[sum((y-m)**2 for y in g)/2 for g,m in zip(groups,actual)]
        # All admissible relabelings that match BOTH mean and sample SD within half a hundredth.
        matches=[perm for perm in permutations(range(6)) if all(abs(actual[j]-reported[i])<=F(1,200)
              and (sds[i]-F(1,200))**2<=var[j]<=(sds[i]+F(1,200))**2 for i,j in enumerate(perm))]
        out[year]=dict(actual_means=list(map(str,actual)),printed_means=list(map(str,reported)),replicates=[[str(v) for v in g] for g in groups],
                       compatible_permutations=[[LABELS[j] for j in p] for p in matches],
                       differences_from_rows=list(map(str,film(actual))),differences_from_summary=list(map(str,film(reported))),
                       interaction_from_rows=interaction(groups),interaction_under_relabelings=[interaction([groups[j] for j in p]) for p in matches])
    require(out['2024']['compatible_permutations']==[list(LABELS)],'2024 matching')
    require(out['2025']['compatible_permutations']==[['CK','T1','T2','T4','T3','T5']],'2025 matching')
    return out

if __name__=='__main__':
    raw=Path(sys.argv[1] if len(sys.argv)>1 else 'supplement.zip').read_bytes()
    print(json.dumps(audit(raw),indent=2,sort_keys=True))
