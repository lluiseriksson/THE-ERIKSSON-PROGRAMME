"""Verify conditional signs in the reported sharp bounds and their joint-count cutoffs."""
from fractions import Fraction as Q
from pathlib import Path
import json
from tasknet_bounds import ROWS, solve

def need(v):
    if not v:raise ValueError('Inconsistent disclosure result')
if __name__=='__main__':
    data=json.loads(Path('bounds.json').read_text());signs={}
    cutoffs={'Lawyers':4,'Elementary School Teachers':5,'Personal Care Aides':3}
    for name,row in ROWS.items():
        exact=solve(row);need(json.loads(json.dumps(exact,default=str))==data[name]);signs[name]={}
        for tab in exact['tables']:
            k=tab['counts'][0];t=Q(k,row[0]);lo=tab['lower'][0]-t;hi=tab['upper'][0]-t
            flag='increase' if lo>0 else 'decrease' if hi<0 else 'zero' if lo==hi==0 else 'ambiguous'
            signs[name][k]=flag
            if name in cutoffs:
                need(flag==('decrease' if k>=cutoffs[name] else 'ambiguous' if k else 'zero'))
                if 0<k<cutoffs[name]:need(lo<0<hi)
            elif name=='Software Developers':need(flag=='increase')
            elif name=='Emergency Medicine Physicians':need(flag==('decrease' if k else 'zero'))
            else:need(flag=='zero')
    print(json.dumps(signs,sort_keys=True))