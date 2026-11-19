from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import json,zipfile,hashlib
# Published table 7 ordered as printed. Costs are IDR in table 8.
ns=[102960,4356,10201,5151,2601]
sizes=[16,1,1,1,1]
densities=[6435,4356,10201,5151,2601]
N=sum(ns);A=401564900;B=616326000
assert N==125269 and sum(sizes)==20 and ns==[a*d for a,d in zip(sizes,densities)]
assert 72000000+125269000+20000000==217269000
assert A==184295900+217269000 and B==399057000+217269000
def strict(q):return q.numerator//q.denominator+1
R=N-ns[0];pooled=strict(Q(N*(A+B),B))
s=strict(Q(A*R,B-A))
assert (B-A)*(s-1)-A*R<=0<(B-A)*s-A*R
assert B*(pooled-1-N)-A*N<=0<B*(pooled-N)-A*N
masks=[]
for mask in product((0,1),repeat=5):
 U=sum((1-k)*n for k,n in zip(mask,ns));M=N-U
 best=B*M-A*U
 worst=-A*N
 # Extremizing over each measured pair independently, and then over all unobserved outcomes:
 # the best possible observed audit has all measured nursery seedlings established, zero bought.
 assert (best>0)==bool(mask[0])
 eq=(B-A)*M-A*U
 assert (eq>0)==bool(mask[0])
 masks.append(dict(measured=list(mask),measured_n=M,can_certify=best>0,max_lower=best,max_equal_lower=eq))
# Fixed-cost share F at design count; all other items scale linearly to 100000 positions.
k=Q(100000,N);gov=24879600
def cost(C,F):return (k*C+(1-k)*F)/20
def cross(C):return (20*gov-k*C)/(1-k)
threshold=cross(B)
assert cost(B,0)<gov and cost(B,20000000)<gov<cost(B,72000000)
assert cost(A,92000000)<gov
assert cost(B,threshold)==gov
assert Q(A,B)*N < ns[0] and (B-A)*sum(ns[1:])<A*ns[0]
r=dict(n=N,smaller=R,costs=[A,B],cost_ratio=str(Q(A,B)),minimum_equal_count=s,dominant_stratum_survival_at_cut=str(Q(s,ns[0])),pooled_threshold=pooled,received_both_per_stratum=False,common_horizon_required=True,patterns=masks,first_any_nursery_only=strict(Q(A*N,B)),gov_budget_per_ha=gov,critical_fixed_cost=str(threshold),cost_per_ha={str(F):str(cost(B,F)) for F in [0,20000000,72000000,92000000]},local_upper_at_92m=str(cost(A,92000000)),p0_gap=B-A)
p=Path('/content/feasibility.zip')
with zipfile.ZipFile(p,'x',zipfile.ZIP_DEFLATED) as z:z.writestr('result.json',json.dumps(r,indent=2))
print('archive_sha256 '+hashlib.sha256(p.read_bytes()).hexdigest())
