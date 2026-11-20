"""Recompute and compare the frontier to its frozen rational results."""
from contextlib import redirect_stdout
from fractions import Fraction as F
from pathlib import Path
import io,json
import serving_frontier as sf

def main():
    stream=io.StringIO()
    with redirect_stdout(stream):sf.main()
    r=json.loads(stream.getvalue())
    sf.need(r==json.loads(Path('frontier.json').read_bytes()),'Frontier differs from the original run')
    rates=json.loads(Path('source.json').read_bytes())['rates_tokens_per_second']
    d=[1/F(str(a))-1/F(str(b)) for a,b in rates.values()]
    p=[F(1,len(d)) for _ in d]
    m=json.loads(Path('mixture.json').read_bytes())['0'];rad=F(m['radius'])
    q=sf.shifted(p,d,rad)
    sf.need(q==list(map(F,m['mix'])) and sf.dot(q,d)==0 and sf.tv(q,p)==rad,'Equal-length transfer differs')
    print(json.dumps(r,indent=2,sort_keys=True))

if __name__=='__main__':main()

