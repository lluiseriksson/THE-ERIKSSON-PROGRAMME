"""Compare every shared adjacent-year observation in Ghana's 2024 CRT archive."""
from decimal import Decimal as D
from pathlib import Path
import hashlib,io,json,re,zipfile
import xml.etree.ElementTree as E
from ghana_trends import direction

DIGEST='8e251bfc976d4ba0b79bcc84d15ac602957e777b5df3c1677dfd602fda562677'
EPS=D('.000001')

def need(ok,msg):
    if not ok:raise ValueError(msg)

def data_sheet(book,num,strings):
    tree=E.fromstring(book.read('xl/worksheets/sheet%d.xml'%num))
    return {c.get('r'):(strings[int(v.text)] if c.get('t')=='s' else v.text) for c in tree.findall('.//{*}c') if (v:=c.find('{*}v')) is not None}

def run_archive(raw):
    need(hashlib.sha256(raw).hexdigest()==DIGEST,'Unrecognized CRT archive')
    series={};summaries={}
    with zipfile.ZipFile(io.BytesIO(raw)) as ar:
        for path in sorted(ar.namelist()):
            if not path.endswith('.xlsx'):continue
            year=int(re.search(r'-V0\.1-(\d{4})-',path).group(1))
            with zipfile.ZipFile(io.BytesIO(ar.read(path))) as book:
                ss=[''.join(i.itertext()) for i in E.fromstring(book.read('xl/sharedStrings.xml'))]
                m=data_sheet(book,48,ss);a=data_sheet(book,55,ss);d=data_sheet(book,60,ss)
                need(m['K1']==str(year) and 'without LULUCF' in m['J71'] and 'with LULUCF' in m['J72'],'Summary headers')
                need('without LULUCF' in a['B71'] and 'without LULUCF' in d['B21'],'Trend labels')
                summaries[year]=[D(m['K71']),D(m['K72'])]
                sub={}
                for k,v in d.items():
                    if not re.fullmatch('[A-Z]+8',k) or not re.fullmatch('(?:19|20)[0-9]{2}',v or ''):continue
                    j=k[:-1];t=int(v)
                    need(a[k]==v, 'Year mismatch')
                    sub[t]=dict(s1n=D(a[j+'71']),s1w=D(a[j+'72']),s6n=D(d[j+'21']),s6w=D(d[j+'22']))
                need(sorted(sub)==list(range(1990,year+1)),f'{year} calendar {sorted(sub)}')
                series[year]=sub
    need(sorted(series)==list(range(1990,2023)),'Missing workbooks')
    names=['s1n','s1w','s6n','s6w'];disagreements={};maxdiff={}
    for k in names:
        changes={};ext={}
        for t in range(1991,2023):
            ds=[(a[t][k]-a[t-1][k],v) for v,a in series.items() if v>=t]
            lo,hi=min(ds),max(ds)
            if direction(lo[0],EPS)*direction(hi[0],EPS)==-1:
                changes[t]=dict(low=str(lo[0]),low_book=lo[1],high=str(hi[0]),high_book=hi[1],last=str(series[2022][t][k]-series[2022][t-1][k]))
            ext[t]=[str(lo[0]),lo[1],str(hi[0]),hi[1]]
        disagreements[k]=changes;maxdiff[k]=ext
    diagonal={year:{k:str(v) for k,v in d[year].items()} for year,d in series.items()}
    diag_eq={k:[y for y,d in series.items() if abs(d[y][k]-summaries[y][int(k.endswith('w'))])>EPS] for k in names}
    return dict(years=len(series),comparisons_per_channel=sum(len(s)-1 for s in series.values()),varying_sign=disagreements,all_ranges=maxdiff,diagonal=diagonal,summary_disagrees=diag_eq)

if __name__=='__main__':
    import sys
    file=Path(sys.argv[1]) if len(sys.argv)>1 else Path('/content/ghana-crt.zip')
    print(json.dumps(run_archive(file.read_bytes()),sort_keys=True,indent=2))


