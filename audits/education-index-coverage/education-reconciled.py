"""Reconcile electronic selection and backward snowballing against six frozen library exports."""
from collections import Counter
from pathlib import Path
from urllib.parse import quote, unquote, urlsplit, parse_qs
from urllib.request import urlopen
from itertools import combinations
from io import BytesIO
import hashlib, json, re, unicodedata, html
import openpyxl
import bibtexparser
from bibtexparser.bparser import BibTexParser

def key(s):
    t=unicodedata.normalize('NFKC',html.unescape(str(s or ''))).casefold()
    return ' '.join(''.join(c if c.isalnum() else ' ' for c in t if c not in '{}').split())

def doi(s):
    st=str(s or '').strip()
    if st.startswith(('https://','http://')):
        loc=urlsplit(st)
        pairs=parse_qs(loc.query)
        vals=pairs.get('doi',[]) or pairs.get('DOI',[])
        st=vals[0] if vals else unquote(loc.path)
    m=re.search(r'10\.\d{4,9}/[^\s>"{}]+',st,re.I)
    return m.group(0).casefold().rstrip('.,;') if m else None

def get(f):
    with urlopen('https://zenodo.org/api/records/16185787/files/'+quote(f['key'],safe='')+'/content',timeout=45) as r:
        raw=r.read(f['size']+1)
    assert len(raw)==f['size'] and 'md5:'+hashlib.md5(raw).hexdigest()==f['checksum']
    return raw

def analyze():
    fs=json.loads(Path('second-register-files.json').read_text())['files']
    wb=openpyxl.load_workbook(BytesIO(get(next(f for f in fs if f['key'].endswith('.xlsx')))),read_only=True,data_only=True)
    rows=[list(sh.values)[1:] for sh in wb];stage1={r[0]:r for r in rows[0] if str(r[0]).startswith('Id_') and str(r[3])=='1'}
    screened={r[0]:r for r in rows[1] if r[0] and r[2] and str(r[3]) in ('0','1')}
    assert stage1.keys()==screened.keys() and all(key(stage1[k][2])==key(r[2]) for k,r in screened.items())
    accepted={k:r for k,r in screened.items() if str(r[3])=='1'}
    snow=[r for r in rows[2] if str(r[2]).upper()=='YES']
    groups={'initial':[(k,r[2],doi(r[9])) for k,r in accepted.items()],
            'backward':[(f'ref-{i}',r[1],doi(r[5]) or doi(r[8])) for i,r in enumerate(snow,1)],
            'preliminary':[(k,r[2],doi(r[10])) for k,r in stage1.items()]}
    tgt={key(t) for g in groups.values() for k,t,d in g}
    sources={};stats={}
    for f in fs:
        if not f['key'].endswith('.bib') or 'duplicate removal' in f['key']:continue
        name=f['key'].removeprefix('Mind the gap_').removesuffix('.bib')
        raw=get(f).decode('utf-8-sig',errors='strict')
        parser=BibTexParser(common_strings=True,ignore_nonstandard_types=False)
        entries=bibtexparser.loads(raw,parser=parser).entries
        raw=raw.replace('\r\n','\n').replace('\r','\n')
        chunks=re.split(r'(?im)^[ \t]*@(?=[a-z]+\s*[{(])',raw)[1:]
        chunks=[x for x in chunks if not re.match(r'(?i)(comment|string|preamble)\s*[{(]',x)]
        rawindex=[]
        for chunk in chunks:
            def field(n):
                m=re.search(r'(?im)(?:^|,)[ \t\n]*'+n+r'\s*=\s*[{"]',chunk)
                if not m:return ''
                sep=chunk[m.end()-1];start=m.end();depth=1
                for pos in range(start,len(chunk)):
                    ch=chunk[pos]
                    if ch=='{' and sep=='{':depth+=1
                    if ch=='}' and sep=='{':depth-=1
                    if depth==0 or (sep=='"' and ch=='"' and chunk[pos-1]!='\\'):return chunk[start:pos]
                return ''
            rawindex.append((key(field('title')),doi(field('doi')) or doi(field('url'))))
        stats[name]=dict(entries=len(entries),declared=len(chunks),without_title=sum(not e.get('title') for e in entries),raw_missing_title=sum(not t for t,d in rawindex))
        parsed=[(key(e.get('title')),doi(e.get('doi')) or doi(e.get('url'))) for e in entries]
        sources[name]=list(set(rawindex+parsed))
    ss=sorted(sources)
    def analyze_group(g):
        masks=[]
        for k,t,d in g:
            matches={};conflicts=[]
            for s,lib in sources.items():
                for u,v in lib:
                    if d and d==v:matches[s]='doi'
                    elif key(t)==u:
                        if d and v and d!=v:conflicts.append([s,v])
                        elif s not in matches:matches[s]='title'
            masks.append(dict(id=k,title=t,doi=d,matches=matches,conflicts=conflicts))
        def portfolios(all_sources):
            eligible=[m for m in masks if set(m['matches'])&set(all_sources)]
            out=[]
            for i in range(len(all_sources)+1):
                for p in combinations(all_sources,i):
                    out.append(dict(portfolio=p,covered=sum(bool(set(p)&set(m['matches'])) for m in eligible)))
            opts=[x for x in out if x['covered']==len(eligible)]
            return dict(union=len(eligible),minimum=[x['portfolio'] for x in opts if len(x['portfolio'])==len(opts[0]['portfolio'])],loss={s:sum(set(m['matches'])&set(all_sources)=={s} for m in eligible) for s in all_sources},all=out)
        return dict(rows=masks,six=portfolios(ss),shared=portfolios(['acm','IEEE Xplore','scopus']))
    print(json.dumps(dict(sources=stats,stage_one=len(stage1),assessed_final=len(screened),groups={k:analyze_group(g) for k,g in groups.items()}),indent=2,ensure_ascii=False))
if __name__=='__main__':analyze()
