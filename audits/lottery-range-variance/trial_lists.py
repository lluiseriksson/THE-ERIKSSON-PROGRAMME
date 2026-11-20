from collections import defaultdict
from itertools import product
from zipfile import ZipFile,ZIP_DEFLATED
from io import StringIO
import csv
from pathlib import Path
import json,hashlib

def make(x,expected):
    n=len(x)
    def profiles(values):
        bins=defaultdict(list);reverse={}
        for i,row in enumerate(product(values,repeat=4)):
            g=(min(row),max(row),sum(row));q=sum(a*a for a in row)
            bins[g].append((q,i));reverse[i]=(g,q,row)
        return bins,reverse
    a,ra=profiles(tuple(range(n)));b,rb=profiles(x)
    pairs=[];left=[];right=[]
    for g in sorted(set(a)|set(b)):
        low=sorted(a[g]);high=sorted(b[g]);i=j=0;skip=[]
        while i<len(low) and j<len(high):
            if low[i][0]<high[j][0]:
                pairs.append((low[i][1],high[j][1],1));i+=1;j+=1
            else:skip.append(high[j][1]);j+=1
        unused_a=[z for _,z in low[i:]]
        unused_b=skip+[z for _,z in high[j:]]
        if tuple(x)==tuple(range(n)):
            assert len(unused_a)==len(unused_b)
            pairs.extend((ai,bi,0) for ai,bi in zip(unused_a,unused_b))
        else:
            left.extend(unused_a);right.extend(unused_b)
    assert sum(flag for _,_,flag in pairs)==expected and len(left)==len(right)
    pairs.extend((i,j,0) for i,j in zip(sorted(left),sorted(right)))
    assert sorted(i for i,_,_ in pairs)==sorted(j for _,j,_ in pairs)==list(range(n**4))
    out=StringIO(newline='');writer=csv.writer(out,lineterminator='\n')
    writer.writerow(['base_ticket_index','alternative_ticket_index','matched','a1','a2','a3','a4','b1','b2','b3','b4'])
    example=None
    for i,j,flag in sorted(pairs):
        g,q,l=ra[i];h,r,u=rb[j]
        assert flag==int(g==h and q<r)
        writer.writerow([i,j,flag,*l,*u])
        if flag and example is None:example={'base':l,'alternative':u,'common_statistics':g,'increase_sum_of_squares':r-q}
    return out.getvalue().encode(),example

INPUTS=[('control-8', [0, 1, 2, 3, 4, 5, 6, 7], 1566), ('control-16', [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], 39942), ('alternative-8', [0, 0, 2, 4, 5, 5, 5, 7], 546), ('alternative-16', [0, 1, 2, 2, 3, 5, 7, 8, 9, 10, 10, 10, 11, 13, 14, 15], 23352)]
def check_formula(n):
    from collections import defaultdict
    from itertools import combinations_with_replacement
    from math import factorial,prod
    maxima=defaultdict(int)
    for row in combinations_with_replacement(range(n),4):
        key=(row[0],row[3],sum(row))
        # Within a cell, the sum of squares determines the two inner values.
        wt=24//prod(factorial(z) for z in Counter(row).values())
        maxima[key]=max(wt,maxima[key])
    fail=sum(maxima.values())
    assert fail==8*n**3-32*n**2+67*n-54
    return n**4-fail
if __name__=='__main__':
    from collections import Counter
    result={n:check_formula(n) for n in range(2,33)}
    p=Path('/content/archive.zip')
    cert={}
    with ZipFile(p,'w',ZIP_DEFLATED) as z:
        for label,x,expected in INPUTS:
            raw,example=make(tuple(x),expected)
            reader=csv.DictReader(StringIO(raw.decode()))
            equal=0
            for row in reader:
                a,b=[[int(row[arm+str(j)]) for j in range(1,5)] for arm in ('a','b')]
                equal+=int((min(a),max(a),sum(a))==(min(b),max(b),sum(b)))
            if label.startswith('control'):assert equal==len(x)**4 and expected==result[len(x)]
            z.writestr(label+'.csv',raw)
            cert[label]=dict(x=x,matched=expected,matched_controls=equal,rows=len(x)**4,sha256=hashlib.sha256(raw).hexdigest(),example=example)
        z.writestr('certificate.json',json.dumps(dict(formula=result,lists=cert),indent=2))
    print('archive_sha256',hashlib.sha256(p.read_bytes()).hexdigest())
