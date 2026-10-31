"""Finite falsification probes of proof.md, not a proof or Lean oracle.
Run only on owned Colab Linux. Acceptance never depends on assert.
"""
import itertools, json, sys
import numpy as np

def require(ok, message):
    if not bool(ok):
        raise RuntimeError(message)

def case(d,n,R):
    shape=(n,)*d
    x=np.indices(shape)
    ks=list(itertools.product(range(1,R+1),*[range(-R,R+1)]*(d-1)))
    V=n**d
    fields=[]; expected=[]; wrong=[]
    rng=np.random.default_rng(20261031+d*100+n)
    w=rng.random((d,d)+shape)
    # Each mean exactly M, spikes allowed to grow with volume.
    M=1.75
    w[:]=0
    for i in range(d):
        for l in range(d):
            pos=tuple(rng.integers(0,n,size=d))
            w[(i,l)+pos]=M*V
    means=w.reshape(d,d,V).mean(axis=2)
    for k in ks:
        angles=2*np.pi*np.array(k)/n
        t=1-np.exp(-1j*angles)
        s=np.exp(1j*angles)-1
        h=np.sqrt(abs(t[0])**2+abs(t[1])**2)
        require(h>0,'zero polarization norm')
        p=np.zeros(d,dtype=complex);p[0]=t[1]/h;p[1]=-t[0]/h
        phase=np.exp(2j*np.pi*sum(k[j]*x[j] for j in range(d))/n)
        u=p.reshape((d,)+(1,)*d)*phase/np.sqrt(V)
        fields.extend((u,1j*u))
        lam=float(np.sum(abs(s)**2))
        q=lam+float(np.sum(abs(s)[:,None]**2*abs(p)[None,:]**2*means))
        expected.extend((q,q))
        pf=np.zeros(d,dtype=complex)
        hf=np.sqrt(abs(s[0])**2+abs(s[1])**2)
        pf[0]=s[1]/hf;pf[1]=-s[0]/hf
        wrong.append(pf.reshape((d,)+(1,)*d)*phase/np.sqrt(V))
    A=np.array(fields)
    H=len(A)
    flat=A.reshape(H,-1)
    gram=(flat.conj()@flat.T).real
    gram_error=float(np.max(abs(gram-np.eye(H))))
    div=np.zeros((H,)+shape,dtype=complex)
    grad_energy=np.zeros(H);repair=np.zeros(H)
    for i in range(d):
        div += A[:,i]-np.roll(A[:,i],1,axis=i+1)
        g=np.roll(A,-1,axis=i+2)-A
        grad_energy += np.sum(abs(g.reshape(H,-1))**2,axis=1)
        repair += np.sum((abs(g)**2*w[i][None,...]).reshape(H,-1),axis=1)
    diagonal=grad_energy+repair
    trace_error=float(np.max(abs(diagonal-np.array(expected))))
    divergence_error=float(np.max(abs(div)))
    B=4*np.pi**2*d*R**2/n**2
    require(gram_error<1e-10,'Gram mismatch')
    require(divergence_error<1e-10,'actual backward divergence nonzero')
    require(trace_error<1e-9,'actual gradient/mean identity mismatch')
    require(float(sum(diagonal))<=H*(1+M)*B+1e-8,'trace bound fails')
    wrong=np.array(wrong);baddiv=np.zeros((len(wrong),)+shape,dtype=complex)
    for i in range(d):
        baddiv += wrong[:,i]-np.roll(wrong[:,i],1,axis=i+1)
    bad_symbol_detected=float(np.max(abs(baddiv)))>1e-5
    require(bad_symbol_detected,'forward/backward mutation not rejected')
    require(float(np.max(abs(2*gram-np.eye(H))))>0.5,'norm mutation not rejected')
    require(abs(sum(expected)/2-sum(diagonal))>1e-5,'real factor mutation not rejected')
    return dict(d=d,n=n,R=R,V=V,H=H,gram_error=gram_error,
        divergence_error=divergence_error,trace_error=trace_error,
        max_weight=float(w.max()),max_spatial_mean=float(means.max()),
        trace=float(sum(diagonal)),trace_bound=float(H*(1+M)*B),
        mutations_rejected=['wrong divergence symbol','missing V normalization','missing real factor two'])

result=[case(*a) for a in [(2,5,1),(2,7,2),(3,5,1),(3,7,2),(4,5,1)]]
print(json.dumps(dict(status='FINITE_PROBES_PASS_NOT_A_PROOF',optimized=not __debug__,
    cases=result,numpy=np.__version__,python=sys.version,universal_proof='proof.md',
    formal_verification=False,independent_review=False),sort_keys=True))
