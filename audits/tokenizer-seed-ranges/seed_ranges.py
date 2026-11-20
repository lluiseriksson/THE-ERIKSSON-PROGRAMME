"""Enclose the infimum of the seed-wise token/character range from rounded triplets."""
from decimal import Decimal as D, localcontext
from pathlib import Path
import json

N=128
PAD=D('1e-28')

def shapes(n, population):
    # Standardize the sorted vector (0,h,1) to unit SD.
    factor=D('1.5').sqrt() if population else D(1)
    vals=[]
    for k in range(n+1):
        h=D(k)/n
        scale=factor/(3*(1-h+h*h)).sqrt()
        vals.append(((-1-h)*scale,(2*h-1)*scale,(2-h)*scale))
    return vals

def mesh(m,s,b,t,Z):
    logs=[tuple(1/(m+s*u).ln() for u in z) for z in Z]
    bpcs=[tuple(b+t*u for u in z) for z in Z]
    winner=None
    for i,(a0,a1,a2) in enumerate(logs):
        for j,(b0,b1,b2) in enumerate(bpcs):
            v0=a0*b0; v1=a1*b1; v2=a2*b2
            width=max(v0,v1,v2)-min(v0,v1,v2)
            if winner is None or width<winner[0]:winner=(width,i,j)
    return winner

def solve(row):
    m,s,b,t=map(D,row['moments'])
    dm=ds=D('.05');db=dt=D('.0005')
    root2=D(2).sqrt();ln2=D(2).ln()
    L=m-dm-root2*(s+ds);U=m+dm+root2*(s+ds)
    l=L.ln();u=U.ln();maxB=b+db+root2*(t+dt)
    if L<=1 or b-db<=root2*(t+dt):raise ValueError('Positive domain required')
    # All bounds below are for the natural-log ratio before converting units.
    Q=maxB/(L*l*l)
    lip_angle=4*(s+ds)*Q+4*(t+dt)/l
    lip_print=2*Q*dm+2*root2*Q*ds+(1/l-1/u)*db+2*root2/l*dt
    by_mode={}
    for name,pop in [('sample',False),('population',True)]:
        Z=shapes(N,pop)
        a,i,j=mesh(m,s,b,t,Z)
        lower=max(D(0),ln2*(a-lip_angle/(2*N)-lip_print)-PAD)
        upper=ln2*a+PAD
        st,tt=s+ds*D('.999'),t-dt*D('.999')
        a2,i2,j2=mesh(m,st,b,tt,Z)
        if ln2*a2+PAD<upper:
            upper=ln2*a2+PAD;i,j=i2,j2
        else:st,tt=s,t
        ppl=[m+st*z for z in Z[i]];bpc=[b+tt*z for z in Z[j]]
        witness=[ln2*x/y.ln() for x,y in zip(bpc,ppl)]
        if abs(max(witness)-min(witness)-upper)>2*PAD:raise ValueError('Witness verification failed')
        for v,mu,sd in [(ppl,m,st),(bpc,b,tt)]:
            if abs(sum(v)/3-mu)>PAD or abs(sum((x-mu)**2 for x in v)/(3 if pop else 2)-sd*sd)>PAD:raise ValueError('Moment witness failed')
        by_mode[name]=dict(lower=str(lower),upper=str(upper),grid_indices=[i,j],sd_pair=list(map(str,[st,tt])),ppl=list(map(str,ppl)),bpc=list(map(str,bpc)))
    lo=min(D(x['lower']) for x in by_mode.values());hi=min(D(x['upper']) for x in by_mode.values())
    return dict(language=row['language'],tokenizer=row['tokenizer'],lower=str(lo),upper=str(hi),by_convention=by_mode)

def main():
    with localcontext() as ctx:
        ctx.prec=48
        rows=json.loads(Path('published-moments.json').read_bytes())
        data=[solve(r) for r in rows]
        print(json.dumps(dict(mesh_intervals=N,units='tokens per character',rows=data),indent=2))
if __name__=='__main__':main()

