"""Check a homogeneous ridge recursion on a frozen synthetic panel. Run in Colab."""
from fractions import Fraction as F
from pathlib import Path
from urllib.request import urlopen
import hashlib
import json
import numpy as np
from sklearn.linear_model import Ridge
from bean_label_scale import URL, DIGEST, partitions, require

ROOT = Path(__file__).resolve().parent

def floating_class():
    with urlopen(URL, timeout=30) as response:
        raw = response.read()
    require(hashlib.sha256(raw).hexdigest() == DIGEST, "Unexpected upstream notebook")
    source = "".join(json.loads(raw)["cells"][5]["source"]).split("    def get_depth_vs_pred_mse", 1)[0]
    original = "self._base_loss(y) < 1e-6"
    require(source.count(original) == 1, "Stopping rule changed")
    scope = dict(np=np, Ridge=Ridge)
    exec(compile(source.replace(original, "self._base_loss(y) < self.threshold"), "pinned-training", "exec"), scope)
    class Corrected(scope["CART"]):
        def fit(self, X, y):
            scale = np.max(np.abs(y))
            self.threshold = 1e-6 * (scale**2 if scale else 1)
            return super().fit(X, y)
        def _get_linear_weights(self, X, y, candidate_feat, combo_feat_idx):
            design = X[:, [combo_feat_idx, candidate_feat]]
            rms = np.sqrt(np.mean(design**2, axis=0))
            used = rms > 0
            weights = np.zeros(2)
            if used.any():
                scaled = design[:, used] / rms[used]
                weights[used] = Ridge(alpha=self.lambda_, fit_intercept=False).fit(scaled, y).coef_ / rms[used]
            return weights
    return Corrected

def exact_tree(X, y, weighted):
    """Exact ordered interval enumeration, using the source's first-wins comparison."""
    rows = {}
    decisions = {}
    nfeatures = len(X[0])
    def variance(ids):
        vals = [y[i] for i in ids]
        mean = sum(vals) / len(vals)
        return sum((v-mean)**2 for v in vals) / len(vals)
    maximum = max(map(abs, y))
    threshold = (maximum**2 if weighted and maximum else F(1)) / 1000000
    def visit(ids, prior, remaining, path):
        rows[path] = list(ids)
        n = len(ids)
        if len(path) == 4 or n < 2 or variance(ids) < threshold:
            return
        best = None
        for f in remaining:
            x = [X[i][f] for i in ids]
            if prior is None:
                score = x
            else:
                z = prior
                a, d = sum(v*v for v in z), sum(v*v for v in x)
                a += a/n if weighted else 1
                d += d/n if weighted else 1
                e = sum(v*t for v,t in zip(z,x))
                h = sum(v*y[i] for v,i in zip(z,ids))
                k = sum(v*y[i] for v,i in zip(x,ids))
                if a and d:
                    det = a*d-e*e
                    u,v = (d*h-e*k)/det, (a*k-e*h)/det
                else:
                    u,v = (h/a if a else F(0)),(k/d if d else F(0))
                score = [u*s+v*t for s,t in zip(z,x)]
            values = sorted(set(score))
            if len(values)<2:
                continue
            bounds = [values[0], *[(s+t)/2 for s,t in zip(values,values[1:])], values[-1]]
            for j,lo in enumerate(bounds):
                for hi in bounds[j+1:]:
                    mask = [lo<=s<=hi for s in score]
                    left = [i for i,included in zip(ids,mask) if included]
                    right = [i for i,included in zip(ids,mask) if not included]
                    if not left or not right:
                        continue
                    loss = (len(left)*variance(left)+len(right)*variance(right))/n
                    if best is None or loss<best[0]:
                        best = loss,f,left,right,mask,score,lo,hi
        if best is None:
            return
        _,feat,left,right,mask,score,lo,hi = best
        decisions[path] = (feat,lo,hi)
        remaining = [v for v in remaining if v!=feat]
        visit(left,[s for s,m in zip(score,mask) if m],remaining,path+"L")
        visit(right,[s for s,m in zip(score,mask) if not m],remaining,path+"R")
    visit(list(range(len(y))),None,list(range(nfeatures)),"")
    return rows,decisions

def delta(a,b):
    return sorted((p for p in a.keys() | b.keys() if a.get(p)!=b.get(p)),key=lambda p:(len(p),p))

def run():
    panel=json.loads((ROOT/"panel.json").read_text())
    X,y=np.array(panel["X"]),np.array(panel["y"])
    rational_X=[[F(v) for v in row] for row in panel["X"]]
    rational_y=list(map(F,panel["y"]))
    factors=[F(1,2),F(1),F(3,2),F(2),F(10)]
    exact,decisions=exact_tree(rational_X,rational_y,True)
    baseline,_=exact_tree(rational_X,rational_y,False)
    raw_scaled,_=exact_tree(rational_X,[F(3,2)*v for v in rational_y],False)
    cls=floating_class()
    def fit(target):
        return cls(max_depth=4,min_samples_split=2,lambda_=1).fit(X,target)
    base=fit(y)
    float_base=partitions(base,X)
    cases={}
    for c in factors:
        eq,branches=exact_tree(rational_X,[c*v for v in rational_y],True)
        require(eq==exact,"Exact partitions differ")
        for path,(f,lo,hi) in decisions.items():
            k=c if path else F(1)
            require(branches[path]==(f,k*lo,k*hi),"Exact split or threshold differs")
        model=fit(float(c)*y)
        fp=partitions(model,X)
        cases[str(c)]=dict(float_changed_paths=delta(float_base,fp),float_vs_exact_paths=delta(exact,fp),
                           max_training_gap=float(np.max(np.abs(base.predict(X)-model.predict(X)/float(c)))),
                           partitions=fp)
    return dict(factors=[str(c) for c in factors],exact_partitions=exact,exact_splits=len(decisions),
                exact_unmodified_changed_paths=delta(baseline,raw_scaled),
                float_base_partitions=float_base,cases=cases)
if __name__=="__main__":
    print(json.dumps(run(),sort_keys=True))
