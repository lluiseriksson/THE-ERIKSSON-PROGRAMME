"""Paired fixed-effects logistic sensitivity with player-cluster sandwich covariance."""
import hashlib,json,csv,zipfile,io,tempfile,os
from pathlib import Path
from statistics import NormalDist
import numpy as np,pandas as pd,requests
from scipy.special import expit
from threadpoolctl import threadpool_limits

def refit(source,model,coef,keep_first,path):
    digest=hashlib.sha256()
    with requests.get(source['url'],params={'p':source['path'],'dl':'1'},stream=True,timeout=(18,70)) as rr,path.open('wb') as out:
        rr.raise_for_status()
        for chunk in rr.iter_content(8*1024*1024):out.write(chunk);digest.update(chunk)
    if digest.hexdigest()!=source['sha256'] or path.stat().st_size!=source['size']:raise ValueError('Snapshot identity')
    df=pd.read_csv(path,usecols=['id','trial','first','second','decision','delta_cbu','delta_emp'])
    df.sort_values(['id','trial'],inplace=True,ignore_index=True,kind='stable')
    if df.duplicated(['id','trial']).any():raise ValueError('Ambiguous trial')
    if keep_first:
        df=df.loc[~df.duplicated(['id','first','second'])].copy()
        progress=df.groupby('id',sort=False).cumcount().to_numpy()
    else:progress=df['trial'].to_numpy()
    ids,gr=pd.factorize(df['id'],sort=True);y=df['decision'].to_numpy()
    if len(gr)!=29493 or len(ids)!=4691033 or not set(np.unique(y))=={0,1}:raise ValueError('Frame mismatch')
    p=(progress-float(model['progress_reference_mean']))/float(model['progress_reference_sd'])
    c=(df['delta_cbu'].to_numpy()-float(model['cbu_reference_mean']))/float(model['cbu_reference_sd'])
    e=(df['delta_emp'].to_numpy()-float(model['emp_reference_mean']))/float(model['emp_reference_sd'])
    design=np.column_stack((e,c,p,e*p,c*p));del df,c,p,e
    beta=np.array(coef);start=beta.copy()
    for step in range(12):
        prob=expit(design@beta);res=y-prob;H=(design.T*(prob*(1-prob)))@design
        update=np.linalg.solve(H,design.T@res)
        if max(abs(update))<1e-11: break
        beta+=update
    else:raise ValueError('Newton fit failed')
    u,s=float(model['progress_reference_mean']),float(model['progress_reference_sd'])
    root=u-s*beta[1]/beta[4];grad=np.array([0,-s/beta[4],0,0,s*beta[1]/(beta[4]**2)])
    # Linearize each root using its own model Hessian and sum row scores within player.
    leverage=design@np.linalg.solve(H,grad)
    scores=np.bincount(ids,weights=leverage*res,minlength=len(gr))
    if abs(scores.sum())>1e-4:raise ValueError('Score residual')
    return gr,scores,dict(root=root,root_at_published=float(model['zero_crossing_progress']),reference_singular=model['singular_fit'],max_coef_change=float(max(abs(beta-start))),hessian_condition=float(np.linalg.cond(H)),steps=step,model_based_se=float(np.sqrt(grad@np.linalg.solve(H,grad))),cluster_se=float(np.linalg.norm(scores)),coefficients=beta.tolist())
def run():
    src=json.loads(Path('inputs.json').read_bytes())
    zpath=Path('source.zip')
    if hashlib.sha256(zpath.read_bytes()).hexdigest()!=src['rep_sha256']:raise ValueError('Release identity')
    with zipfile.ZipFile(zpath) as z:
        def rows(n):return list(csv.DictReader(io.StringIO(z.read(next(k for k in z.namelist() if k.endswith('/outputs/decomposition/'+n+'.csv'))).decode())))
        meta=rows('model_metadata');coeff=rows('model_coefficients')
    parts=[];groups=[];models=[]
    with tempfile.TemporaryDirectory() as tmp,threadpool_limits(limits=2):
        for label,nm in [('S1','S1_common_unique'),('S4','S4_first_occurrences_unique_common')]:
            m,=[r for r in meta if r['model_id']==nm];terms={r['term']:float(r['estimate']) for r in coeff if r['model_id']==nm}
            gr,sc,d=refit(src[label],m,[terms[k] for k in ['emp_z','cbu_z','progress_z','emp_z:progress_z','cbu_z:progress_z']],label=='S4',Path(tmp)/'snapshot.csv')
            groups.append(gr);parts.append(sc);models.append(d)
    if not np.array_equal(*groups):raise ValueError('Unpaired player sets')
    V=np.array(parts)@np.array(parts).T
    contrast=parts[1]-parts[0];se=float(np.linalg.norm(contrast));shift=float(models[1]['root']-models[0]['root'])
    if abs(se**2-(V[0,0]+V[1,1]-2*V[1,0]))>1e-6:raise ValueError('Covariance mismatch')
    ordered=np.sort(contrast**2)[::-1]
    crit=NormalDist().inv_cdf(.975)
    return dict(estimand='Zero-random-intercept logistic sensitivity, common scaling held fixed, CR0 sandwich clustered on matched players. No cluster correction or bootstrap.',models=models,players=len(groups[0]),rows_per_fit=4691033,covariance=V.tolist(),correlation=float(V[1,0]/np.sqrt(V[0,0]*V[1,1])),se=se,shift=shift,interval=[shift-crit*se,shift+crit*se],largest_cluster_variance_share=float(ordered[0]/sum(ordered)),largest_ten_variance_share=float(sum(ordered[:10])/sum(ordered)),input_sha256={k:src[k]['sha256'] for k in ('S1','S4')})
if __name__=='__main__':print(json.dumps(run(),sort_keys=True))
