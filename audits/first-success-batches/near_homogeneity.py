from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
import hashlib,json
import sympy as S

def main():
    x,y,b=S.symbols('p1 p2 b')
    probabilities=lambda p: [(1-p)**2,p,p*(1-p)]
    z=[[0,0,0],[0,1,1],[0,1,3]]
    signed=[[0,1,-1],[1,1,1],[-1,1,1]]
    def expect(weights):
        return sum(u*v*weights[i][j] for i,u in enumerate(probabilities(x)) for j,v in enumerate(probabilities(y)))
    t=S.symbols('t');pg=S.Poly((1-x+x*t)**2*(1-y+y*t)**2,t)
    target=sum(pg.nth(k) for k in range(2,5))
    assert S.expand(expect(z)-target+(x-y)**2)==0
    assert S.expand(expect(signed)-target)==0
    assert S.expand((1-b)*expect(z)+b*expect(signed)-target+(1-b)*(x-y)**2)==0
    # General label-symmetric scores with diagonal unbiasedness.
    a,c,d,e,f,g=S.symbols('a c d e f g')
    weights=[[a,c,d],[c,e,f],[d,f,g]]
    bias=S.Poly((expect(weights)-target).subs(y,x),x)
    sol=S.linsolve(bias.all_coeffs(),(a,c,d,e,f,g))
    assert len(sol)==1
    coeff=next(iter(sol));assert coeff[0]==0 and S.simplify(coeff[1]+coeff[2])==0
    data=dict(conditional_means=list(map(str,coeff)),symmetry='failure, early, late in rows and columns',bias='-(p1-p2)^2',uniform_loss='1-b')
    path=Path('/content/archive.zip')
    with ZipFile(path,'w',ZIP_DEFLATED) as zf:zf.writestr('identities.json',json.dumps(data))
    print('archive_sha256',hashlib.sha256(path.read_bytes()).hexdigest())
if __name__=='__main__':main()
