"""Finite exact checks of unit129; own Colab Linux only. Not a universal proof."""
from fractions import Fraction as F
from collections import Counter
from math import isqrt
import hashlib
import json
import platform
import time


def require(condition, message):
    if not condition:
        raise ValueError(message)


def power(value, D):
    v=F(value); result=v**(D//2)
    if D%2:
        a,b=isqrt(v.numerator),isqrt(v.denominator)
        require(a*a==v.numerator and b*b==v.denominator,'non-square rational fixture')
        result*=F(a,b)
    return result


def mode(L,cycle,drop_cycle_edge=False):
    require(L>=2,'mode length')
    values=[F(min(t,L-t) if cycle else t) for t in range(L)]
    mean=sum(values,F(0))/L
    values=[v-mean for v in values]
    variance=sum((v*v for v in values),F(0))
    edges=range(L if cycle and not drop_cycle_edge else L-1)
    energy=sum(((values[(t+1)%L]-values[t])**2 for t in edges),F(0))
    if not cycle:
        want_norm=F(L*(L*L-1),12);want_energy=F(L-1)
    else:
        m=L//2;want_energy=F(2*m)
        want_norm=F(m*(m*m+2),6) if L%2==0 else F(m*(m+1)*(m*m+m+1),3*(2*m+1))
    require(sum(values,F(0))==0 and variance==want_norm,'mode norm/mean identity')
    require(energy==want_energy,'mode forward-edge energy identity')
    require(energy/variance<=F(48,L*L),'mode Rayleigh bound')
    return values,energy,variance


def shift(x,i,amount,n):
    y=list(x);y[i]=(y[i]+amount)%n;return tuple(y)


def detours(n,D,weak,force_bad_direction=False):
    occupied=Counter()
    for x in weak:
        for i in range(D):
            j=1 if i==0 else (i+1 if i<D-1 else 1)
            if force_bad_direction:j=0
            require(j!=i,'detour repeats replaced direction')
            tail=shift(x,j,-1,n);last=shift(tail,i,1,n)
            require(tail not in weak and last not in weak,'weak detour tail')
            occupied[(tail,j)]+=1;occupied[(tail,i)]+=1;occupied[(last,j)]+=1
    require(max(occupied.values(),default=0)<=5,'congestion bound')
    return max(occupied.values(),default=0)


def sparse_energies(n,D,weak,A,b,u,weaken_incoming=False):
    tails=set(u)
    for x in u:
        tails.update(shift(x,i,-1,n) for i in range(D))
    unit=F(0);weighted=F(0);incoming=F(0)
    for x in tails:
        for i in range(D):
            y=shift(x,i,1,n);delta=u.get(y,F(0))-u.get(x,F(0))
            value=delta*delta;weight=b if x in weak else A
            if weaken_incoming and x not in weak and y in weak:weight=b
            unit+=value;weighted+=weight*value
            if i>=1 and x not in weak and y in weak:incoming+=weight*value
    norm=sum((v*v for v in u.values()),F(0))
    require(incoming==(D-1)*A*norm,'incoming boundary identity')
    require(weighted>=A*unit/16,'coupled form comparison')
    return unit,weighted,incoming,norm


def profile(D,n,b,gamma):
    require(F(b)**D==n*n,'exact b=n^(2/D) fixture')
    f=F(n,n**D);mu=F(gamma*n*n);A=(mu-f*b)/(1-f)
    require(1<=b<=mu<=A<=2*mu,'profile coefficient range')
    require(f*b+(1-f)*A==mu,'exact mean')
    weak={(s,)+(0,)*(D-1) for s in range(n)}
    require(F(n)/power(b,D)==1,'weak inverse critical mass')
    require(f*power(mu/F(b),D)==power(gamma,D),'weak moment contribution')
    require(A>=mu and A/F(n*n)>=gamma,'global comparison coefficient')
    congestion=detours(n,D,weak)
    count=0;failed_blocks=0
    for L in range(2,n+1):
        values,energy,variance=mode(L,L==n)
        u={(s,)+(0,)*(D-1):v for s,v in enumerate(values)}
        require(sum(u.values(),F(0))==0,'actual block mean')
        unit,weighted,incoming,norm=sparse_energies(n,D,weak,A,F(b),u)
        decoupled=F(b)*energy
        require(norm==variance and weighted>=incoming,'sparse energy/norm')
        if gamma*L*L>48*b:
            require(decoupled<gamma*norm,'required local-certificate failure absent')
        if decoupled<gamma*norm:failed_blocks+=1
        count+=1
    return {'D':D,'n':n,'b':b,'gamma':gamma,'A_exact':str(A),
            'moment_upper_exact':str(power(gamma,D)+1),'congestion':congestion,
            'block_witnesses':count,'decoupled_failures_at_c_gamma':failed_blocks}


def main():
    require(platform.system()=='Linux','own Colab Linux only')
    start=time.perf_counter();mode_count=0
    for L in range(2,65):
        for cycle in (False,True):mode(L,cycle);mode_count+=1
    cases=[profile(D,n,b,gamma) for D,n,b in
           ((3,8,4),(3,27,9),(4,4,2),(4,9,3),(5,32,4),(6,8,2))
           for gamma in (1,4,9)]
    mutations=[]
    try:mode(5,True,drop_cycle_edge=True)
    except ValueError as e:
        require(str(e)=='mode forward-edge energy identity','unexpected mode mutation error')
        mutations.append('omitted periodic occurrence')
    n,D=6,3;weak={(s,0,0) for s in range(n)}
    try:detours(n,D,weak,force_bad_direction=True)
    except ValueError:mutations.append('invalid detour direction')
    try:sparse_energies(n,D,weak,F(100),F(1),{(0,0,0):F(1)},weaken_incoming=True)
    except ValueError as e:
        require(str(e)=='incoming boundary identity','unexpected boundary mutation error')
        mutations.append('incoming strong weight erased')
    require(len(mutations)==3,'mutation accepted')
    report={'status':'finite_exact_checks_passed','path_cycle_modes':mode_count,
            'profile_cases':len(cases),'actual_block_witnesses':sum(c['block_witnesses'] for c in cases),
            'profiles':cases,'mutations_rejected':mutations,'arithmetic':'exact Fraction',
            'scope':'unit129 finite identities only; not universal/Lean proof or independent review',
            'elapsed_seconds':time.perf_counter()-start,'platform':platform.platform()}
    payload=json.dumps(report,sort_keys=True,separators=(',',':'))
    print('REPORT_JSON_BEGIN');print(payload);print('REPORT_JSON_END')
    print('REPORT_SHA256',hashlib.sha256(payload.encode()).hexdigest())


if __name__=='__main__':main()
