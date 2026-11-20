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
results={}
for name,power in [('printed_24',1),('invariant',.5)]:
    weights={}
    for label,c in [('pi',pi),('eta',eta),('etap',etap)]:
        w=integral(K,K,c,power,True)
        assert abs(w-integral(K,K,c,power,False))<5e-12
        alt=integral(K,c,K,power,True)
        weights[label]=dict(KK_first=w,spectator_K=alt)
        if name=='invariant': assert abs(w-alt)<1e-12
    ref=weights['pi']['KK_first']
    results[name]=dict(phase=weights,eta_to_KKpi=(2/3)*eta_amp**2*weights['eta']['KK_first']/ref,etap_to_KKpi=(2/3)*etap_amp**2*weights['etap']['KK_first']/ref,eta_to_etap=(eta_amp/etap_amp)**2*weights['eta']['KK_first']/weights['etap']['KK_first'])
num=2*1.8051e-10
den=2*(8.9358e-9+4.4679e-9)
data=dict(reference='10.1140/epjc/s10052-026-16450-0',masses_GeV=[M,K,pi,eta,etap],angle_degrees=39.3,amplitudes_relative_to_muK2_mupi=[eta_amp,etap_amp],results=results,individual_width_ratios=[num/den,2*2.5830e-9/den],printed_summary=[.135,.193])
with zipfile.ZipFile('/content/archive.zip','w',zipfile.ZIP_DEFLATED) as z:z.writestr('ratios.json',json.dumps(data,indent=2))
print('archive_sha256',hashlib.sha256(Path('/content/archive.zip').read_bytes()).hexdigest())
