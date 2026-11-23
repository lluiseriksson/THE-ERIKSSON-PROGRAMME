"""Independently verify least degrees and strict negativity throughout each interval."""
import copy,gzip,json,math,subprocess,sys
from fractions import Fraction as F
from pathlib import Path

def require(v,msg):
    if not v:raise ValueError(msg)

def check(w,index):
    x=F(w['parameter']);s=w['shift'];q=x.denominator
    P=[int(v,16) for v in w['coefficients_hex']]
    n=len(P)-1
    require(x==F(index['parameter']) and n==index['first_degree'] and q==w['scaling_q'] and P[-1]>0,'shape')
    left,right=map(F,w['interval'])
    require(0<=left<x<right<=1,'endpoints')
    require(right-x==x-left==(1-x)/2**w['halvings'],'frozen interval')
    square=[0]*(2*n+1)
    for i,a in enumerate(P):
        for j,b in enumerate(P):square[i+j]+=a*b
    d=2*n+s
    mon=[sum(square[k-s]*q**(k-s)*math.comb(k,j)**2*math.comb(k+j,j)**2
             for k in range(max(j,s),d+1)) for j in range(d+1)]
    value=sum(v*x**k for k,v in enumerate(mon))*q**s
    require(value==int(w['direct_form_hex'],16) and value<0,'point value')
    # Two changes of basis, independent of homogeneous Horner generation.
    den=math.lcm(left.denominator,right.denominator)
    a=int(left*den);span=int((right-left)*den)
    power=[span**i*sum(mon[j]*math.comb(j,i)*a**(j-i)*den**(d-j) for j in range(i,d+1)) for i in range(d+1)]
    bern=[sum(power[i]*math.comb(d-i,k-i) for i in range(k+1)) for k in range(d+1)]
    require(max(bern)<0,'Bernstein positivity test on negative form')
    return n

def main():
    r=json.loads(Path('results.json').read_bytes())
    witnesses=json.loads(gzip.decompress(Path('witnesses.json.gz').read_bytes()))
    tasks=[];expected=[]
    for row in r['points']:
        x=F(row['parameter'])
        for item in row['forms']:
            k=item['first_negative_degree'];last=row['limit'] if k is None else k
            tasks.append(f"{x.numerator} {x.denominator} {item['shift']} {last}")
            expected.append([1]*item['earlier_positive']+([] if k is None else [-1]))
    subprocess.run(['g++','-std=c++17','-O2','apery-minors.cpp','-lgmpxx','-lgmp','-o','bareiss'],check=True)
    out=subprocess.check_output(['./bareiss'],input='\n'.join(tasks)+'\n',text=True,timeout=450)
    signs=[list(map(int,line.split())) for line in out.splitlines()]
    require(signs==expected,'independent Sylvester signs')
    require(len(witnesses)==len(r['points'])==6,'case count')
    for w,row in zip(witnesses,r['points']):
        require(row['first_degree']==min(x['first_negative_degree'] for x in row['forms'] if x['first_negative_degree'] is not None),'joint degree')
        require(any(f['shift']==w['shift'] and f['first_negative_degree']==row['first_degree'] for f in row['forms']),'first shift')
        check(w,row)
    for field,new in [('direct_form_hex','0x0'),('scaling_q',17),('interval',['0','1']),('coefficients_hex',['0x1'])]:
        changed=copy.deepcopy(witnesses[0]);changed[field]=new
        try:check(changed,r['points'][0])
        except ValueError:continue
        raise ValueError('mutation accepted '+field)
    print(json.dumps(dict(status='verified',python_optimized=not __debug__,forms=len(tasks),leading_minors=sum(map(len,signs)),intervals=len(witnesses),rejected_mutations=4)))
if __name__=='__main__':main()