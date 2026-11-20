"""Reconstruct bibliographic database coverage from the exact title/status register."""
from collections import Counter,defaultdict
from pathlib import Path
from itertools import combinations
import json,unicodedata,hashlib,statistics
import fitz
def require(test,msg):
    if not test:raise ValueError(msg)
def extract():
    doc=fitz.open('source.pdf');rows=[];issues=[];pages={}
    for p in doc:
        lines=[]
        for block in p.get_text('rawdict')['blocks']:
            for line in block.get('lines',[]):
                chars=[ch for sp in line['spans'] for ch in sp['chars']]
                for lower,upper in [(0,164),(164,501.8),(501.8,790)]:
                    part=[ch for ch in chars if lower<=ch['origin'][0]<upper]
                    s=''.join(ch['c'] for ch in part).strip()
                    if s:lines.append((part[0]['origin'][0],(line['bbox'][1]+line['bbox'][3])/2,s))
        status=sorted((y,s) for x,y,s in lines if x<160 and y>96)
        hist=Counter(s for y,s in status)
        require(set(hist)<={'Accepted','Rejected','Duplicated'},('status',p.number,hist))
        require(status,('empty-page',p.number))
        src=[[] for _ in status];titles=[[] for _ in status]
        for x,y,s in lines:
            if y<96 or x<160:continue
            i=min(range(len(status)),key=lambda j:abs(y-status[j][0]))
            if abs(y-status[i][0])>17.5:issues.append([p.number+1,x,y,s[:35],'alignment'])
            (titles if x<497 else src)[i].append((y,s))
        for i,(y,s) in enumerate(status):
            title=' '.join(t for _,t in sorted(titles[i]));source=' '.join(t for _,t in sorted(src[i]))
            if not title or source not in {'ACM Digital Library','IEEE Digital Library','Scopus'}:issues.append([p.number+1,i+1,s,'missing field'])
            rows.append(dict(page=p.number+1,row=i+1,status=s,title=title,source=source))
        if hist['Accepted']:pages[str(p.number+1)]=hist['Accepted']
    return rows,issues,pages
def key(t,mode):
    v=' '.join(unicodedata.normalize('NFKC',t).casefold().split())
    if mode=='tokens':v=' '.join(''.join(c if c.isalnum() else ' ' for c in v).split())
    return v
def summarize(rows,mode):
    g=defaultdict(list)
    for r in rows:g[key(r['title'],mode)].append(r)
    target={k:v for k,v in g.items() if any(r['status']=='Accepted' for r in v)}
    def coverage(positive):
        masks={k:{r['source'] for r in v if r['status'] in positive} for k,v in target.items()}
        allsrc=sorted({s for ss in masks.values() for s in ss})
        subs=[list(a) for i in range(len(allsrc)+1) for a in combinations(allsrc,i) if all(set(a)&s for s in masks.values())]
        opt=min(map(len,subs))
        return dict(sources=allsrc,minimum_sets=[a for a in subs if len(a)==opt],only={s:sum(v=={s} for v in masks.values()) for s in allsrc},available={s:sum(s in v for v in masks.values()) for s in allsrc},observed_incidence=sum(map(len,masks.values()))),masks
    a,x=coverage({'Accepted'});b,y=coverage({'Accepted','Duplicated'})
    return dict(accepted_titles=len(target),representatives=a,including_duplicates=b,extra_titles=sum(x[k]!=y[k] for k in x),accepted_rejected_conflicts=sum(any(r['status']=='Rejected' for r in v) for v in target.values()),table=[dict(page=v[0]['page'],title_sha256=hashlib.sha256(k.encode()).hexdigest(),sources=sorted(y[k]),representatives=sorted(x[k])) for k,v in target.items()])
def main():
    rows,issues,pages=extract()
    out=dict(row_count=len(rows),status_counts=dict(Counter(r['status'] for r in rows)),source_counts=dict(Counter(r['source'] for r in rows)),issues=issues,accepted_pages=pages)
    if not issues:out['comparisons']={m:summarize(rows,m) for m in ['primary','tokens']}
    print(json.dumps(out,sort_keys=True,indent=2))
if __name__=='__main__':main()