"""Bounds over all response roundings conditional on the printed design. No lot model."""
import runpy, contextlib, io, json
import numpy as np
with contextlib.redirect_stdout(io.StringIO()):
    first=runpy.run_path('mineral-margin.py')
X,Y,coef,printed=(first[k] for k in ['X','Y','coef','printed'])
B=np.linalg.pinv(X)
assert np.max(np.abs(B@Y-coef))<1e-12
def interval(w,y):
    mean=w@y
    rad=0.005*abs(w).sum()
    return [float(mean-rad),float(mean+rad)]
vertices=first['centers'][1:]
out={}
for col,(name,t) in enumerate(zip(first['out'][0]['margins'],first['thresholds'])):
    label=['iron','calcium','zinc'][col]
    y=Y[:,col];a=B@y
    vertices_domain=np.eye(3)*70+10
    if all(interval(x@B,y)[0]>t for x in vertices_domain):
        out[label]={'attainable':False}
        continue
    i,j=int(a.argmax()),int(a.argmin())
    for k in range(3):
        if k!=i:assert interval(B[i]-B[k],y)[0]>0
        if k!=j:assert interval(B[k]-B[j],y)[0]>0
    den=B[i]-B[j]
    def endpoint(c,which):
        lo,hi=0,50
        for _ in range(65):
            r=(lo+hi)/2; f=interval(c@B-r*den,y)[which]-t
            if f>0:lo=r
            else:hi=r
        w=c@B-hi*den
        ext=y+(1 if which else -1)*np.sign(w)*.005
        r=(c@B@ext-t)/(den@ext)
        assert abs(r-hi)<1e-8 and c[i]-r>=10 and c[j]+r<=80
        return float(r)
    out[label]=dict(donor=i,recipient=j,minimum=min(endpoint(c,0) for c in vertices),maximum=max(endpoint(c,1) for c in vertices))
c=first['centers'][0];intervals=[interval(c@B,Y[:,k]) for k in range(3)]
# Separate response columns allow simultaneous adjustments. Check the rounded printed predictions jointly.
w=c@B
for k,target in enumerate(first['out'][0]['predicted']):
    displayed=[4.11,162.56,2.36][k]
    lower=max(displayed-.005,intervals[k][0]);upper=min(displayed+.005,intervals[k][1])
    assert lower<upper
    perturb=((lower+upper)/2-target)*np.sign(w)/sum(abs(w))
    assert max(abs(perturb))<.005 and abs(w@(Y[:,k]+perturb)-displayed)<.005
print(json.dumps(dict(margins=out,prediction_bounds=intervals,rounding_witness=True,scope='Fixed printed experimental designs; response means within half a hundredth; arbitrary nonnegative completion of the 0.02 g deficit; dry-basis mineral targets only. These are deterministic compatibility bounds.')))