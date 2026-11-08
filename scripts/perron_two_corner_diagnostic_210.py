# SPDX-License-Identifier: AGPL-3.0-only
"""Exact finite source-weight/symmetric-similarity and gap-bound diagnostics.
Not a proof of the all-L limit, Lean verification, or a physical spectral gap.
Run on the programme's owned Colab Linux runtime, not the owner's desktop.
"""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path


def ldl_psd(matrix, strict=False):
    n=len(matrix)
    if any(matrix[i][j]!=matrix[j][i] for i in range(n) for j in range(n)):
        return False,[]
    low=[[F(int(i==j)) for j in range(n)] for i in range(n)];diag=[]
    for j in range(n):
        pivot=matrix[j][j]-sum((low[j][k]**2*diag[k] for k in range(j)),F(0))
        if pivot<0 or (strict and pivot==0):return False,diag+[pivot]
        diag.append(pivot)
        for i in range(j+1,n):
            residual=matrix[i][j]-sum((low[i][k]*low[j][k]*diag[k] for k in range(j)),F(0))
            if pivot==0:
                if residual!=0:return False,diag
                low[i][j]=F(0)
            else:low[i][j]=residual/pivot
    return True,diag


def make(q,L):
    if not F(0)<q<F(1) or type(L) is not int or L<1:
        raise ValueError('q must be in(0,1), integerL>=1')
    n=1<<L;R=(1+q)**L;z=q**L;t=z*z/R
    d=[F(1) if i in (0,n-1) else t for i in range(n)]
    H=[[q**((i^j).bit_count()) for j in range(n)] for i in range(n)]
    S=[[d[i]*H[i][j]*d[j] for j in range(n)] for i in range(n)]
    A=[[d[i]**2*H[i][j] for j in range(n)] for i in range(n)]
    return n,R,z,t,d,H,S,A


def check_case(q,L):
    n,R,z,t,d,H,S,A=make(q,L);corners=(0,n-1);eta=2*z*z+z**4/R
    checks=0
    for i in range(n):
        if sum(H[i],F(0))!=R or sum((H[j][i] for j in range(n)),F(0))!=R:
            raise ValueError('Exact row/column sum mismatch')
        for j in range(n):
            if H[i][j]<=0 or S[i][j]<=0 or A[i][j]<=0:
                raise ValueError('Strict positivity failure')
            if A[i][j]*d[j]/d[i]!=S[i][j]:
                raise ValueError('Wrong source-weight convention/similarity')
            B=H[i][j] if i in corners and j in corners else F(0)
            P_H_Q=H[i][j] if i in corners and j not in corners else F(0)
            Q_H_P=H[i][j] if i not in corners and j in corners else F(0)
            Q_H_Q=H[i][j] if i not in corners and j not in corners else F(0)
            if S[i][j]-B!=t*(P_H_Q+Q_H_P)+t*t*Q_H_Q:
                raise ValueError('Rank-two decomposition mismatch')
            checks+=1
    if H[0][0]!=1 or H[-1][-1]!=1 or H[0][-1]!=z:
        raise ValueError('Corner compression mismatch')
    if (S[0][0]+S[-1][-1]+2*S[0][-1])/2!=1+z:
        raise ValueError('Top Rayleigh witness mismatch')
    # Exact LDL certificates of the relevant finite variational inequalities.
    top=[[(1+z+eta)*int(i==j)-S[i][j] for j in range(n)] for i in range(n)]
    second=[[(1-z+eta)*int(i==j)-S[i][j]+(z if i in corners and j in corners else 0) for j in range(n)] for i in range(n)]
    pivots={}
    for name,M in [('H_positive_definite',H),('S_positive_definite',S),('lambda1_upper',top),('lambda2_upper_with_corner_rank1',second)]:
        ok,ds=ldl_psd(M,strict=name in ('H_positive_definite','S_positive_definite'))
        if not ok:raise ValueError('Exact finite PSD certificate failed: '+name)
        pivots[name]=[str(v) for v in ds]
    return {'q':str(q),'L':L,'dimension':n,'R':str(R),'z':str(z),'t':str(t),'eta':str(eta),'delta_lower':str((2*z-eta)/(1+z)),'delta_upper':str((2*z+eta)/(1+z+eta)),'entry_checks':checks,'ldl_pivots':pivots}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    cases=[check_case(q,L) for q in (F(1,3),F(1,2),F(2,3)) for L in (1,2,3,4)]
    negatives=[]
    for q in (F(0),F(1)):
        try:make(q,2)
        except ValueError:negatives.append('excluded_q_'+str(q))
        else:raise ValueError('Invalid q accepted')
    n,R,z,t,d,H,S,A=make(F(1,2),2)
    wrong=[[(1-z)*int(i==j)-S[i][j] for j in range(n)] for i in range(n)]
    if ldl_psd(wrong)[0]:raise ValueError('Incorrect top-eigenvalue upper bound accepted')
    negatives.append('wrong_lambda1_upper')
    if all((H[i][j]*d[j]**2)*d[j]/d[i]==S[i][j] for i in range(n) for j in range(n)):
        raise ValueError('Target/column weighting mistaken for source/row weighting')
    negatives.append('wrong_weight_orientation')
    if len(cases)!=12 or len(negatives)!=4:raise ValueError('Explicit completion count mismatch')
    result={'status':'EXACT_FINITE_DIAGNOSTICS_VALIDATED','cases':cases,'case_count':len(cases),'entry_count':sum(c['entry_checks'] for c in cases),'negative_guards':negatives,'normal_or_optimized':'normal' if __debug__ else 'optimized','case_certificate_sha256':hashlib.sha256(json.dumps(cases,sort_keys=True,separators=(',',':')).encode()).hexdigest(),'general_analytic_proof':'Separate source note;12finite cases do not prove the all-L asymptotic','lean_replay':False,'new_scientific_assessment':False,'physical_or_continuum_conclusion':False}
    args.out.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:v for k,v in result.items() if k!='cases'}))

if __name__=='__main__':main()
