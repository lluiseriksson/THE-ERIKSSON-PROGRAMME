"""Sharp benchmark tradeoffs for selective insertion of Arabic case vowels."""
from pathlib import Path
from fractions import Fraction as F
import itertools,json,zipfile
with zipfile.ZipFile('zenodo_p2.zip') as archive:
    def read(n):return json.loads(archive.read('zenodo_p2/'+n))
    coarse=read('results_539k.json')
    detail=read('results_539n_stats.json')
n=detail['n']['test']
def exact_count(percent,den):
    target=F(str(percent))
    counts=[x for x in range(den+1) if abs(100*F(x,den)-target)<=F(1,200)]
    if len(counts)!=1:raise ValueError(('Nonunique count',percent,den,counts))
    return counts[0]
points={}
for row in coarse['curve']:
    d=exact_count(row['filled_pct'],n);correct=exact_count(row['acc'],d)
    points[str(row['tau'])]=(d,d-correct)
for row in detail['curve']:
    pair=row['dec'],row['dec']-row['ok'];key=str(row['tau'])
    if key in points and points[key]!=pair:raise ValueError('tables disagree')
    points[key]=pair
ru=detail['test_rules_only'];points['rules']=(ru['dec'],ru['dec']-ru['ok'])
# Rules form a fixed base; assess threshold policies with the same cue rules.
order=sorted(points,key=points.get)
bands=[]
for i,j in zip(order,order[1:]):
    count=points[j][0]-points[i][0];err=points[j][1]-points[i][1]
    if not 0<=err<=count:raise ValueError('Invalid nested decisions')
    bands.append(dict(lo=i,hi=j,size=count,errors=err,rate=str(F(err,count))))
def optimum(at):
    # Permissible selection uses only a threshold band. Equal probabilities
    # inside any partially used band guarantee the displayed expectation.
    budget=at-ru['dec'];e=F(ru['dec']-ru['ok']);plan=[]
    for z in sorted(bands,key=lambda x:F(x['rate'])):
        k=min(budget,z['size']);budget-=k;e+=k*F(z['rate'])
        plan.append([z['lo'],z['hi'],k])
    if budget:raise ValueError('Budget outside source range')
    return dict(errors=str(e),plan=plan)
comparisons={}
for k,(f,err) in points.items():
    opt=optimum(f)
    mixtures=[(F(err),k,k,F(0))]
    for a,b in itertools.combinations(order,2):
        x,y=points[a],points[b]
        if x[0]<f<y[0]:
            w=F(f-x[0],y[0]-x[0]);mixtures.append(((1-w)*x[1]+w*y[1],a,b,w))
    v,a,b,m=min(mixtures)
    comparisons[k]=dict(filled=f,errors=err,optimum=opt,threshold_mixture=dict(errors=str(v),a=a,b=b,weight_b=str(m)))
print(json.dumps(dict(eligible=n,bands=bands,comparisons=comparisons),indent=2))
