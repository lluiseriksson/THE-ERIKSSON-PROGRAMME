import itertools, sys
BAD=[]
for n in (3,4,5):
    for (p,q) in [(0,1),(0,n-1),(1,2)]:
        if p==q or q>=n: continue
        for mu in (0.2,0.7):
            M=[[mu if (a,b) in {(p,q),(q,p)} else 1.0 for b in range(n)] for a in range(n)]
            R={}
            for a,b,c,d in itertools.product(range(n),repeat=4):
                R[(a,b,c,d)]=(M[a][b]*M[c][d])/(M[c][b]*M[a][d])
            lo=min(R.values()); hi=max(R.values())
            tight={k for k,v in R.items() if abs(v-lo)<1e-12}
            argmax={k for k,v in R.items() if abs(v-hi)<1e-12}
            exp_tight={(p,q,q,p),(q,p,p,q)}
            exp_argmax={(p,p,q,q),(q,q,p,p)}
            ok = abs(lo-mu**2)<1e-12 and abs(hi-mu**-2)<1e-12 and tight==exp_tight and argmax==exp_argmax
            if not ok: BAD.append((n,p,q,mu,lo,sorted(tight),sorted(argmax)))
            if (n,p,q,mu)==(3,0,1,0.2):
                print(f"  n=3 p,q=(0,1) mu=0.2:  phi_min={lo:.6f} (=mu^2={mu**2:.6f})   TIGHT={sorted(tight)}")
                print(f"                          Phi_max={hi:.6f} (=mu^-2={mu**-2:.6f})  ARGMAX={sorted(argmax)}")
print()
print("TightSet (LB orientation) and ArgMax (reciprocal) are DISJOINT:",
      exp_tight.isdisjoint(exp_argmax))
print(f"cells failing: {len(BAD)}")
sys.exit(1 if BAD else 0)
