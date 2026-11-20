"""Compare expressions (19),(21),(22),(24)-(30) at the published isospin inputs."""
import hashlib, json, math, zipfile
from pathlib import Path
from itertools import permutations
from scipy.integrate import quad
M=2.359
K=(.493677+.497611)/2
pi=(.1349768+.13957039)/2
eta,etap=.547862,.95778
phi=math.radians(39.3)
muq=1.07
mus=1.34*(2*K*K-pi*pi)/(27.30*pi*pi)
eta_amp=muq*math.cos(phi)/math.sqrt(2)-mus*math.sin(phi)
etap_amp=muq*math.sin(phi)/math.sqrt(2)+mus*math.cos(phi)
def integral(a,b,c,power,transformed):
    lo=(a+b)**2
    hi=(M-c)**2
    def kernel(s):
        p=math.sqrt(max(0,(s-lo)*(s-(a-b)**2)))/(2*math.sqrt(s))
        q=math.sqrt(max(0,(hi-s)*((M+c)**2-s)))/(2*M)
        return p*q/s**power
    if transformed:
        def fun(x):
            return kernel(lo+(hi-lo)*math.sin(x)**2)*(hi-lo)*math.sin(2*x)
        return quad(fun,0,math.pi/2,epsabs=1e-13,epsrel=1e-13)[0]
    return quad(kernel,lo,hi,epsabs=5e-13,epsrel=5e-13,limit=200)[0]
from itertools import product
from scipy.optimize import brentq
from math import atan, asin, degrees, radians, sin, cos, sqrt, hypot
def phase(a,b,c):
    first=integral(a,b,c,.5,True)
    for x,y,z in set(permutations((a,b,c))):
        assert abs(integral(x,y,z,.5,False)-first)<2e-11
    return first
base=phase(K,K,pi)
q0,f0,angle=1.07,1.34,39.3
k=(2*K*K-pi*pi)/(27.30*pi*pi)
eta_weight=(2/3)*phase(K,K,eta)/base
ep_weight=(2/3)*phase(K,K,etap)/base
def amplitudes(q,f,deg):
    v=radians(deg)
    a,b=q/sqrt(2),k*f
    return a*cos(v)-b*sin(v),a*sin(v)+b*cos(v)
def ratio(q,f,deg):
    a,_=amplitudes(q,f,deg)
    return eta_weight*a*a
def box(mult):
    return list(product([q0-.02*mult,q0+.02*mult],[f0-.06*mult,f0+.06*mult],[angle-mult,angle+mult]))
def summary(mult):
    corners=box(mult)
    A=[amplitudes(*p)[0] for p in corners]
    assert max(p[2] for p in corners)<90 and min(p[2] for p in corners)>0 and min(min(p[:2]) for p in corners)>0
    return dict(min_a=min(A),max_a=max(A),lower=0 if min(A)<=0<=max(A) else min(x*x for x in A)*eta_weight,upper=max(x*x for x in A)*eta_weight)
one=summary(1)
assert one['max_a']<0 and one['upper']<.1345
zero=brentq(lambda m:summary(m)['max_a'],1,10)
threshold=brentq(lambda m:summary(m)['upper']-.1345,1,12)
a,b=q0/sqrt(2),k*f0
node=degrees(atan(a/b))
roots=[node+sign*degrees(asin(sqrt(.135/eta_weight)/hypot(a,b))) for sign in [-1,1]]
assert all(abs(ratio(q0,f0,x)-.135)<1e-13 for x in roots)
assert summary(threshold-.001)['upper']<.1345<summary(threshold+.001)['upper']
assert summary(zero+.001)['lower']==0
# Charge-summed amplitudes, in units of mu_K^2 mu_pi (common parent factors cancel).
v=radians(angle)
Q=q0*cos(v);Qp=q0*sin(v);S=-k*f0*sin(v);Sp=k*f0*cos(v)
pi_over_K=(130.2/155.7)*(pi/K)**2*(1+27.30)/2
def normalized(masses,amp,mult): return phase(*masses)*amp**2*mult/(3*base)
full={
 'pipi_eta':normalized((pi,pi,eta),sqrt(2)*pi_over_K**2*Q,1.5),
 'pipi_etap':normalized((pi,pi,etap),sqrt(2)*pi_over_K**2*Qp,1.5),
 'KK_eta':ratio(q0,f0,angle),
 'KK_etap':ep_weight*amplitudes(q0,f0,angle)[1]**2,
 'KK_pi':1.,
 'eta_eta_eta':normalized((eta,eta,eta),sqrt(2)*Q**3*pi_over_K**2,1/6),
 'eta_eta_etap':normalized((eta,eta,etap),pi_over_K**2*(sqrt(2)*Q**2*Qp+2*S**2*Sp),.5)}
whole={'pipi_eta':(5.7264+11.453)*1e-9,'pipi_etap':(2.0188+4.0376)*1e-9,'KK_eta':2*1.8051e-10,'KK_etap':2*2.5830e-9,'KK_pi':(2*8.9358+2*4.4679)*1e-9,'eta_eta_eta':2.7427e-10,'eta_eta_etap':8.1253e-10}
printed=[.641,.226,.135,.193,1.,.010,.030]
out=dict(fks_source='10.1103/PhysRevD.58.114006 eqs 3.11 and 3.15',factor_k=k,central_node_degrees=node,central_angle_solutions=roots,one_error_box=one,first_box_multiple_touching_zero=zero,first_box_multiple_reaching_rounding_band=threshold,rounding_band_lower=.1345,all_ratios=full,by_partial_widths={n:x/whole['KK_pi'] for n,x in whole.items()},out_of_printed_rounding=[n for n,r in zip(full,printed) if abs(full[n]-r)>.0005],joint_confidence_level=None)
with zipfile.ZipFile('/content/archive.zip','w',zipfile.ZIP_DEFLATED) as z:z.writestr('mixing.json',json.dumps(out,indent=2))
print('archive_sha256',hashlib.sha256(Path('/content/archive.zip').read_bytes()).hexdigest())
