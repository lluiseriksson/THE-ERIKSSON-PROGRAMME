"""Run on Linux with NumPy and scikit-learn; fetch only the pinned public notebook."""
from pathlib import Path
from urllib.request import urlopen
import ast
import hashlib
import json
import platform
import numpy as np
import sklearn
from sklearn.linear_model import Ridge

PIN = "c0f5ea1cec8dba55a54039564b5e8104b8c3a69c"
DIGEST = "7598165073559efdd9de89ada744e4f7c803a139eade04c934bfee5ccc063505"
URL = f"https://raw.githubusercontent.com/DavidLin628/Ob-Int-CART/{PIN}/Ob-Int%20CART.ipynb"

def require(test, message):
    if not test:
        raise ValueError(message)

def estimator():
    with urlopen(URL, timeout=30) as response:
        data = response.read()
    require(hashlib.sha256(data).hexdigest() == DIGEST, "Notebook changed")
    lines = "".join(json.loads(data)["cells"][5]["source"]).splitlines()
    stop = next(i for i,line in enumerate(lines) if line.startswith("    def get_depth_vs_pred_mse"))
    module = ast.parse("\n".join(lines[:stop]))
    require([node.name for node in module.body] == ["TreeNode","CART"], "Unexpected source")
    scope = {"np": np, "Ridge": Ridge}
    exec(compile(module, "pinned-training-methods", "exec"),scope)
    return scope["CART"]

def partitions(model, X):
    result = {}
    def visit(node, Xnode, idx, path):
        result[path] = sorted(idx.tolist())
        if node.value is not None:
            return
        scores = model._generate_projection(Xnode,node.feature_idx,node.combo_feat_idx,node.a_opt)
        left = (scores >= node.left_bound) & (scores <= node.right_bound)
        for mask,child,side in [(left,node.left,"L"),(~left,node.right,"R")]:
            visit(child,np.column_stack([Xnode[mask],scores[mask]]),idx[mask],path+side)
    visit(model.root,X,np.arange(len(X)),"")
    return result

def audit():
    Cart = estimator()
    simple_x = np.array([[0],[0],[1],[1]],float)
    simple_y = np.array([1,1,1.0016,1.0016])
    def fit(x,y):
        return Cart(max_depth=4,min_samples_split=2,lambda_=1).fit(x,y)
    require(fit(simple_x,simple_y).root.value is not None and fit(simple_x,1.5*simple_y).root.value is None,"Variance witness")
    corners=np.array([[0,0],[1,0],[0,1],[1,1]],float)
    labels=np.array([10,10,11,11],float)
    m=Cart(lambda_=1)
    scores=[]
    for c in (1,1.5):
        inputs=corners*np.array([c,1])
        beta=m._get_linear_weights(inputs,c*labels,1,0)
        projection=m._generate_projection(inputs,1,0,beta)
        parent=m._base_loss(c*labels)
        gain,_,_=m._evaluate_projection(projection,c*labels,parent)
        scores.append(dict(order=np.argsort(projection).tolist(),best_normalized_loss=float((parent-gain)/c**2)))
    require(scores[0]["order"]==[0,1,2,3] and scores[1]["order"]==[0,2,1,3] and abs(scores[0]["best_normalized_loss"])<1e-12 and abs(scores[1]["best_normalized_loss"]-1/6)<1e-12,"Node witness")
    rng=np.random.default_rng(20261120)
    witness=None
    for trial in range(1,151):
        # Binary fractions keep feature and response inputs exactly representable.
        X=rng.integers(0,17,(24,4))/16
        y=rng.integers(32,129,24)/32
        base,scaled=fit(X,y),fit(X,1.5*y)
        a,b=partitions(base,X),partitions(scaled,X)
        if {p:v for p,v in a.items() if len(p)<=2}!={p:v for p,v in b.items() if len(p)<=2}:
            continue
        diff=sorted(p for p in a.keys()&b.keys() if len(p)==3 and a[p]!=b[p])
        gap=float(np.max(np.abs(base.predict(X)-scaled.predict(X)/1.5)))
        if not diff or gap<0.01:continue
        pos=[float(np.var(y[indices])) for part in (a,b) for indices in part.values() if np.var(y[indices])>0]
        if min(pos)<1e-4:continue
        witness=dict(trial=trial,X=X.tolist(),y=y.tolist(),first_changed_depth=3,changed_paths=diff,original_partitions=a,scaled_partitions=b,largest_normalized_training_prediction_difference=gap,smallest_positive_node_variance_in_original_units=min(pos))
        break
    require(witness is not None,"No registered end-to-end witness within search budget")
    return dict(notebook_sha=PIN,notebook_sha256=DIGEST,numpy=np.__version__,sklearn=sklearn.__version__,python=platform.python_version(),corner_results=scores,variance_witness=True,synthetic_witness=witness)
if __name__=="__main__":
    print(json.dumps(audit(),sort_keys=True,separators=(",",":")))

