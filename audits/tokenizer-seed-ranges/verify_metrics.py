"""Rebuild the three-run bounds, then cross-check exclusion by secant slopes."""
from contextlib import redirect_stdout
from decimal import Decimal as D,localcontext
from pathlib import Path
import json,io
import seed_ranges

def main():
    stream=io.StringIO()
    with redirect_stdout(stream):seed_ranges.main()
    got=json.loads(stream.getvalue())
    if got!=json.loads(Path('ranges.json').read_bytes()):raise ValueError('Range results changed')
    rows=json.loads(Path('published-moments.json').read_bytes())
    with localcontext() as ctx:
        ctx.prec=48
        for row,sol in zip(rows,got['rows'],strict=True):
            m,s,b,t=map(D,row['moments']);hi_s=s+D('.05')
            L=m-D('.05')-2*hi_s;U=m+D('.05')+2*hi_s
            if (b+D('.0005'))*hi_s/(L*L.ln())+D('1e-28')>=t-D('.0005'):raise ValueError('Fixed-density case not excluded')
            if D(sol['lower'])<=0 or D(sol['upper'])<D(sol['lower']):raise ValueError('Invalid range bounds')
    print(json.dumps(got,indent=2,sort_keys=True))
if __name__=='__main__':main()

