"""Independent symbolic design derivation of the next regular K2 head."""
import sympy as sp
from surface_bessel_relative_coefficients_exact import relative_coefficients

N=9
def z(): return [sp.S.Zero]*N
def c(v): return [sp.sympify(v)]+[sp.S.Zero]*(N-1)
def add(a,b): return [x+y for x,y in zip(a,b)]
def neg(a): return [-x for x in a]
def scale(a,v): return [v*x for x in a]
def mul(a,b): return [sum((a[k]*b[n-k] for k in range(n+1)),sp.S.Zero) for n in range(N)]
def inv(a):
    o=z(); o[0]=1/a[0]
    for n in range(1,N): o[n]=-o[0]*sum((a[k]*o[n-k] for k in range(1,n+1)),sp.S.Zero)
    return o
def sqrt_series(a):
    o=z(); o[0]=sp.sqrt(a[0])
    for n in range(1,N): o[n]=(a[n]-sum((o[k]*o[n-k] for k in range(1,n)),sp.S.Zero))/(2*o[0])
    return o
def exp_series(a):
    o=z(); o[0]=sp.exp(a[0])
    for n in range(1,N): o[n]=sum((k*a[k]*o[n-k] for k in range(1,n+1)),sp.S.Zero)/n
    return o
def polynomial(a,coeffs):
    o=c(0)
    for v in reversed(coeffs): o=add(mul(o,a),c(sp.Rational(v.numerator,v.denominator)))
    return o
def derive():
    cvar,sigma,tau=sp.symbols('c sigma tau',positive=True); s2,t2=sigma**2,tau**2; d=[sp.S.Zero,sp.S.One]+[sp.S.Zero]*(N-2)
    def sinc(x2): return [sp.Rational((-1)**n*2**(2*n+1),sp.factorial(2*n+2))*x2/4*(x2/4)**n for n in range(N)]
    p,q=sinc(s2),sinc(t2); w=add(add(p,q),neg(scale(mul(d,mul(p,q)),1/cvar**2))); root=sqrt_series(add(c(1),neg(mul(d,w)))); phase=scale(mul(w,inv(add(c(1),root))),-4*cvar); corr=list(phase); corr[0]=sp.S.Zero; ex=exp_series(corr); invz=scale(mul(d,inv(root)),1/(4*cvar)); acomp=polynomial(invz,relative_coefficients('A',N-1)); bcomp=polynomial(invz,relative_coefficients('B',N-1)); ri=inv(root); rhi=inv(sqrt_series(root)); r3=mul(ri,rhi); r5=mul(mul(ri,ri),rhi); dw=scale(add(c(1),neg(mul(d,add(p,q)))),2); cc=2*cvar**2-1; bracket=add(add(scale(mul(d,p),-2*cc),scale(mul(d,q),-cc)),add(c(2*cc+1),add(scale(mul(mul(d,d),mul(p,q)),2),add(scale(mul(d,p),-1),scale(mul(d,q),-2))))); fo=scale(mul(p,bracket),-4)
    ints={'KD':mul(mul(r3,acomp),mul(dw,ex)),'KF':mul(mul(r3,acomp),mul(fo,ex)),'HDD':mul(mul(r5,bcomp),mul(mul(dw,dw),ex)),'HDF':mul(mul(r5,bcomp),mul(mul(dw,fo),ex))}
    def gauss(expr):
        total=sp.S.Zero
        for (i,j),coef in sp.Poly(sp.expand(expr),sigma,tau).terms():
            if i%2 or j%2: continue
            mi=sp.factorial2(i-1)/cvar**(i//2) if i else 1; mj=sp.factorial2(j-1)/cvar**(j//2) if j else 1; total += coef*mi*mj
        return sp.cancel(total)
    m={name:[gauss(v) for v in vals] for name,vals in ints.items()}; b=add(mul(m['KD'],m['HDF']),neg(mul(m['KF'],m['HDD']))); assert sp.simplify(b[0])==0
    y=scale(mul(b[1:]+[sp.S.Zero],mul(inv(m['KD']),inv(m['KD']))),1/(2*cvar))
    return [sp.factor(v) for v in y[:8]]
if __name__=='__main__':
    vals=derive(); print('R7_DESIGN',vals[6],flush=True); print('R8_DESIGN',vals[7],flush=True); print('DESIGN ONLY',flush=True)
