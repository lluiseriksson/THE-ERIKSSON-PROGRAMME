"""Six fixed floating-point diagnostics on EXACT275 paired subspace; Linux only.
FABRICATION, not a certificate or scientific/novelty/gap claim. Never run on Windows.
"""
import os
if os.name!='posix':raise RuntimeError('277 mathematics runs only in the own Colab Linux runtime')
for _name in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS','VECLIB_MAXIMUM_THREADS']:
    os.environ[_name]='1'
import sys,json,hashlib,traceback,zipfile,time
from pathlib import Path
from datetime import datetime,timezone
import numpy as np
import scipy
import scipy.sparse as sp
import scipy.linalg as la

ROOT=Path('/content/tep277-diagnostic');E=ROOT/'evidence';ZIP=Path('/content/tep277-diagnostic-results.zip')
BASE='801004ccd85170de6b39146decd34cc6400c2060'
RELATIVE_SVD=1e-10;TOL=1e-8
def require(ok,message):
    if not bool(ok):raise ValueError(message)
def utc():return datetime.now(timezone.utc).isoformat()
def finite(a,label):require(np.isfinite(a).all(),'Nonfinite '+label)
def dump(path,value):
    path.write_text(json.dumps(value,indent=2,allow_nan=False)+'\n',encoding='utf-8')
def maxabs(a):return float(np.max(np.abs(a))) if np.size(a) else 0.0
def sparse_max(a):return maxabs(a.data)
def sparse_comparison(a,b):
    diff=(a-b).tocsr();diff.eliminate_zeros()
    return {'absolute_max':sparse_max(diff),'scale':max(1.0,sparse_max(a),sparse_max(b)),'scaled':sparse_max(diff)/max(1.0,sparse_max(a),sparse_max(b))}
def require_comparison(value,label):require(value['scaled']<=TOL,'Assembly comparison failed '+label)

def physical_basis(n):
    """Direct point stencil, sites/component last: A_s(y), B_s(y)."""
    odd=list(range(1,n,2));m=len(odd);N=n*n;d=m*(N-1)+2*(m-1)
    rr=[];cc=[];vv=[]
    def add(s,i,j,r,col,value):
        for shift in [0,1]:
            k=(s-i-j+shift)%n
            rr.append((((i%n)*n+(j%n))*n+k)*3+r);cc.append(col);vv.append(value)
    for si,s in enumerate(odd):
        for q in range(1,N):
            i,j=divmod(q,n);col=si*(N-1)+q-1
            for di,dj,r,value in [(0,0,0,1),(0,1,0,-1),(0,0,1,-1),(1,0,1,1),(1,0,2,-1),(0,1,2,1)]:add(s,i+di,j+dj,r,col,value)
    for si,s in enumerate(odd[:-1]):
        for b in [0,1]:
            col=m*(N-1)+2*si+b
            for i in range(n):
                for j in range(n):
                    for layer,sign in [(s,1),(odd[-1],-1)]:
                        add(layer,i,j,b,col,sign);add(layer,i,j,2,col,-sign)
    B=sp.coo_matrix((np.array(vv,dtype=float),(rr,cc)),shape=(3*n**3,d)).tocsr();B.sum_duplicates();B.eliminate_zeros()
    require(d==n**3//2+n//2-2,'Exact275 dimension mismatch')
    return B

def layer_basis(n):
    """Independent delta-operator construction; layer/component/y ordering."""
    N=n*n;m=n//2;ii=np.arange(N).reshape(n,n);identity=sp.eye(N,format='csr')
    def shift(axis,step):return sp.coo_matrix((np.ones(N),(np.arange(N),np.roll(ii,step,axis=axis).ravel())),shape=(N,N)).tocsr()
    D1=identity-shift(0,1);D2=identity-shift(1,1);gauge=identity[:,1:]
    L=sp.vstack([D2@gauge,-D1@gauge,(D1-D2)@gauge],format='csr')
    potentials=sp.block_diag([L]*m,format='csr');rr=[];cc=[];vv=[]
    for si in range(m-1):
        for b in [0,1]:
            col=2*si+b
            for layer,sign in [(si,1),(m-1,-1)]:
                for q in range(N):
                    for comp,value in [(b,sign),(2,-sign)]:rr.append((layer*3+comp)*N+q);cc.append(col);vv.append(value)
    constants=sp.coo_matrix((vv,(rr,cc)),shape=(m*3*N,2*(m-1))).tocsr()
    return sp.hstack([potentials,constants],format='csr')

def forms(n,B,T):
    """No dense physical Laplacian. Weighted sparse edge application only."""
    x=np.indices((n,n,n));weights=np.where((x.sum(axis=0)%2)==1,float(n*n),1.0/48.0).ravel();w3=np.repeat(weights,3)
    physical_ids=np.arange(3*n**3).reshape(n,n,n,3)
    K=sp.csr_matrix((B.shape[1],B.shape[1]),dtype=float)
    for direction in range(3):
        jump=B[np.roll(physical_ids,-1,axis=direction).ravel(),:]-B
        K=K+jump.T@jump.multiply(w3[:,None])
    G=(B.T@B).tocsr();K=K.tocsr()
    idx=np.arange(T.shape[0]).reshape(n//2,3,n,n);Kalt=sp.csr_matrix(K.shape,dtype=float)
    for axis in [2,3]:
        jump=T[np.roll(idx,-1,axis=axis).ravel(),:]-T
        Kalt=Kalt+float(n*n)*(jump.T@jump)
    next_layer=np.roll(idx,-1,axis=0)
    for axis in [2,3,None]:
        target=next_layer if axis is None else np.roll(next_layer,-1,axis=axis)
        jump=T[target.ravel(),:]-T;Kalt=Kalt+(jump.T@jump)*(1.0/48.0)
    Galt=(T.T@T)*2.0
    comparisons={'G_physical_vs275':sparse_comparison(G,Galt),'K_physical_vs275':sparse_comparison(K,Kalt),'K_symmetry':sparse_comparison(K,K.T),'G_symmetry':sparse_comparison(G,G.T)}
    for label,value in comparisons.items():require_comparison(value,label)
    finite(K.data,'K');finite(G.data,'G')
    return K,G,comparisons

def rows(n,tau):
    """ALL original short/long cells, physical spatial rows, both channels.
    Channel2 rows are identically zero since this exact275 class uses channel1.
    No tau0 total equation is dropped: actual nonempty right/long cells remain.
    """
    rr=[];cc=[];vv=[];lr=[];lc=[];lv=[];labels=[];m=n//2;N=n*n
    for i,cut in enumerate(tau):
        intervals=[list(range(cut)),[int(cut)],list(range(cut+1,n))]
        for interval_name,I in zip(['left','singleton','right'],intervals):
            if not I:continue
            for long,J in [(False,[0]),(True,list(range(1,n)))]:
                norm=1.0/np.sqrt(float(n**3*len(I)*len(J)))
                for channel in [1,2]:
                    for comp in range(3):
                        row=len(labels);labels.append({'slice':i,'tau':int(cut),'x2_interval':interval_name,'x2':I,'x3':'long' if long else 'zero','component':comp+1,'channel':channel,'cell_size':len(I)*len(J),'normalization':float(norm)})
                        if channel==2:continue
                        for j in I:
                            for k in J:rr.append(row);cc.append(((i*n+j)*n+k)*3+comp);vv.append(norm)
                            residue=(i+j)%n;s=residue if residue%2 else (residue-1)%n;si=(s-1)//2
                            if long:
                                for layer in range(m):lr.append(row);lc.append((layer*3+comp)*N+i*n+j);lv.append(2*norm)
                                lr.append(row);lc.append((si*3+comp)*N+i*n+j);lv.append(-norm)
                            else:lr.append(row);lc.append((si*3+comp)*N+i*n+j);lv.append(norm)
    C=sp.coo_matrix((vv,(rr,cc)),shape=(len(labels),3*n**3)).tocsr()
    CL=sp.coo_matrix((lv,(lr,lc)),shape=(len(labels),m*3*N)).tocsr();CL.sum_duplicates();CL.eliminate_zeros()
    return C,CL,labels

def physical_checks(n,u,case,C,labels,theta,layerT,expected_lambda):
    field=u.reshape(n,n,n,3);norm=float(np.sum(field*field));require(norm>0 and np.isfinite(norm),'Zero/nonfinite witness norm')
    x=np.indices((n,n,n));odd=x.sum(axis=0)%2==1;weights=np.where(odd,float(n*n),1.0/48.0)
    q=0.0;qh=0.0;qa=0.0
    for j in range(3):
        jump=np.roll(field,-1,axis=j)-field;point=np.sum(jump*jump,axis=3);qh+=float(n*n*np.sum(point[odd]));qa+=float(np.sum(point[~odd])/48.0);q+=float(np.sum(weights*point))
    direct_rows=[]
    for label in labels:
        if label['channel']==2:direct_rows.append(0.0);continue
        J=[0] if label['x3']=='zero' else list(range(1,n));value=0.0
        for j in label['x2']:
            for k in J:value+=float(field[label['slice'],j,k,label['component']-1])
        direct_rows.append(value*label['normalization'])
    rowvec=np.asarray(C@u).ravel();direct_rows=np.array(direct_rows)
    div=sum(field[...,j]-np.roll(field[...,j],1,axis=j) for j in range(3));mean=np.sum(field,axis=(0,1,2))
    axes=np.arange(n);g1=np.exp(2j*np.pi*axes/n)-1;g=np.stack(np.broadcast_arrays(g1[:,None,None],g1[None,:,None],g1[None,None,:]),axis=-1)
    spectrum=np.fft.fftn(field,axes=(0,1,2),norm='ortho');den=np.sum(np.abs(g)**2,axis=-1);safe=np.where(den>0,den,1)
    pairs=[(0,1),(0,2),(1,2)];Ahat=np.empty((n,n,n,3),dtype=complex)
    for p,(j,l) in enumerate(pairs):Ahat[...,p]=(g[...,j]*spectrum[...,l]-g[...,l]*spectrum[...,j])/safe;Ahat[0,0,0,p]=0
    Avec=np.fft.ifftn(Ahat,axes=(0,1,2),norm='ortho');realA=Avec.real
    reconstructed=np.zeros_like(field)
    for p,(j,l) in enumerate(pairs):
        # A_lj=-A_jl: adjoint is incoming minus source for each A_lj.
        reconstructed[...,j]-=np.roll(realA[...,p],1,axis=l)-realA[...,p]
        reconstructed[...,l]+=np.roll(realA[...,p],1,axis=j)-realA[...,p]
    v=(layerT@theta).reshape(n//2,3,n,n);n275=2*float(np.sum(v*v));h275=0.0;a275=0.0
    for axis in [2,3]:h275+=float(n*n*np.sum((np.roll(v,-1,axis=axis)-v)**2))
    nxt=np.roll(v,-1,axis=0)
    for axis in [2,3,None]:a275+=float(np.sum(((nxt if axis is None else np.roll(nxt,-1,axis=axis))-v)**2)/48.0)
    checks={'row_residual_scaled':maxabs(rowvec)/max(1.0,float(np.linalg.norm(u))),
            'row_direct_vs_matrix_scaled':maxabs(direct_rows-rowvec)/max(1.0,maxabs(rowvec)),
            'backward_divergence_scaled':maxabs(div)/max(1.0,maxabs(field)),
            'global_mean_scaled':maxabs(mean)/max(1.0,n**1.5*float(np.linalg.norm(u))),
            'fft_preimage_imaginary_scaled':maxabs(Avec.imag)/max(1.0,maxabs(realA)),
            'actual_curl_adjoint_reconstruction_scaled':maxabs(reconstructed-field)/max(1.0,maxabs(field)),
            'norm_physical_vs275_scaled':abs(norm-n275)/max(1.0,abs(norm),abs(n275)),
            'Q_physical_vs275_scaled':abs(q-(h275+a275))/max(1.0,abs(q),abs(h275+a275)),
            'Rayleigh_vs_eigensolver_scaled':abs(q/norm-expected_lambda)/max(1.0,abs(q/norm),abs(expected_lambda))}
    for key,value in checks.items():require(np.isfinite(value) and value<=TOL,'Witness integrity check failed '+key)
    for value,name in [(field,'physical witness'),(Ahat,'FFT preimage'),(realA,'real preimage'),(rowvec,'rows')]:finite(value,name)
    np.save(case/'physical-witness.npy',field,allow_pickle=False);np.save(case/'curl-preimage-fft.npy',Ahat,allow_pickle=False);np.save(case/'curl-preimage-real.npy',realA,allow_pickle=False);np.save(case/'observed-rows.npy',rowvec,allow_pickle=False)
    return {'norm_squared':norm,'Q_physical':q,'Q_H_physical':qh,'Q_a_physical':qa,'Rayleigh_Q_over_counting_norm':q/norm,'norm275':n275,'Q_H275':h275,'Q_a275':a275,'checks':checks,'preimage_pair_order':['12','13','23'],'FFT_normalization':'ortho','tolerance':TOL}

def one_case(n,cut_name,B,T,K,G,assembly):
    case=E/(str(n)+'-'+cut_name);case.mkdir();report={'n':n,'cut':cut_name,'c':1.0,'H':n*n,'a':1.0/48,'dimension':B.shape[1],'construction':'EXACT275 paired class, channel1; channel2zero','psi_gauge':'psi_s(0,0)=0','constant_basis':'(1,0,-1),(0,1,-1) per odd layer except last, subtract same from last','assembly_comparisons':assembly,'status':'FAILED_PRESERVED','started_at':utc()}
    try:
        tau=np.array([(2*i*i)%n if cut_name=='nonlinear' else 0 for i in range(n)],dtype=int);report['tau']=tau.tolist();report['F']=[(i+int(tau[i]))%n for i in range(n)]
        C,CL,labels=rows(n,tau);R=(C@B).tocsr();Ralt=(CL@T).tocsr();comp=sparse_comparison(R,Ralt);require_comparison(comp,'all original rows vs276 E/W')
        report.update(original_rows=len(labels),channel2_zero_rows=sum(x['channel']==2 for x in labels),row_assembly_comparison=comp)
        dump(case/'row-labels.json',labels);sp.save_npz(case/'R-original-cells.npz',R)
        dense=R.toarray();U,s,Vh=la.svd(dense,full_matrices=True,check_finite=True,lapack_driver='gesvd');finite(s,'singular values');finite(Vh,'right singular vectors')
        cutoff=RELATIVE_SVD*float(s[0]) if len(s) else 0.0;rank=int(np.sum(s>cutoff));nullity=B.shape[1]-rank
        report['SVD']={'relative_cutoff':RELATIVE_SVD,'absolute_cutoff':cutoff,'all_singular_values':s.tolist(),'rank':rank,'nullity':nullity,'meaning':'Floating-point diagnostic, not an exact rank certificate','driver':'gesvd'}
        del U,dense
        if nullity==0:
            np.save(case/'eigenvector-parameters.npy',np.empty(0),allow_pickle=False);report['status']='NO_NUMERICAL_NULLSPACE_AT_FIXED_CUTOFF';report['minimum_eigenvalue']=None;report['witness']=None
        else:
            Z=Vh[rank:,:].T
            Kz=np.asfortranarray(Z.T@(K@Z));Gz=np.asfortranarray(Z.T@(G@Z));Kz=(Kz+Kz.T)*0.5;Gz=(Gz+Gz.T)*0.5
            finite(Kz,'reduced physicalK');finite(Gz,'reduced physicalG')
            values,vectors=la.eigh(Kz,Gz,subset_by_index=[0,0],driver='gvx',overwrite_a=True,overwrite_b=True,check_finite=True)
            lam=float(values[0]);coeff=vectors[:,0];theta=Z@coeff;u=np.asarray(B@theta).ravel();finite(theta,'eigenvector parameters');finite(u,'witness')
            pivot=int(np.argmax(np.abs(theta)))
            if theta[pivot]<0:theta=-theta;u=-u;coeff=-coeff
            norm=float(np.linalg.norm(u));require(norm>0 and np.isfinite(norm),'Zero generalized witness');theta/=norm;u/=norm;coeff/=norm
            np.save(case/'eigenvector-parameters.npy',theta,allow_pickle=False);np.save(case/'eigenvector-null-coordinates.npy',coeff,allow_pickle=False)
            report['minimum_eigenvalue']=lam;report['witness']=physical_checks(n,u,case,C,labels,theta,T,lam);report['status']='FINITE_FLOATING_DIAGNOSTIC_COMPLETED'
        report['limitations']='Only selected n4,8,16/cuts and exact275 restricted subspace; no rank certificate, continuum/physicalgap/coercivity/novelty proof or adaptive threshold search.'
    except Exception:report['failure']=traceback.format_exc();(case/'failure.txt').write_text(report['failure'],encoding='utf-8')
    finally:report['finished_at']=utc();dump(case/'case.json',report)
    print(json.dumps({'n':n,'cut':cut_name,'status':report['status'],'minimum_eigenvalue':report.get('minimum_eigenvalue')},allow_nan=False),flush=True)
    return report

require(not ROOT.exists() and not ZIP.exists(),'Fresh own diagnostic root/archive required')
E.mkdir(parents=True)
summary={'construction_base':BASE,'script_raw_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'started_at':utc(),'numpy':np.__version__,'scipy':scipy.__version__,'python':sys.version,'fixed_n':[4,8,16],'fixed_cuts':['nonlinear','zero'],'SVD_relative_cutoff':RELATIVE_SVD,'integrity_tolerance':TOL,'math_status':'Exploratory floating-point selected finite diagnostics only','independent_replication':False,'billing_units':None,'cases':[],'status':'FAILED_PRESERVED'}
try:
    for n in [4,8,16]:
        model=E/('model-'+str(n));model.mkdir();B=physical_basis(n);T=layer_basis(n);K,G,assembly=forms(n,B,T)
        sp.save_npz(model/'B-physical.npz',B);sp.save_npz(model/'K-physical.npz',K);sp.save_npz(model/'G-physical.npz',G)
        dump(model/'assembly.json',{'n':n,'B_shape':list(B.shape),'B_nnz':int(B.nnz),'K_nnz':int(K.nnz),'G_nnz':int(G.nnz),'comparisons':assembly,'no_dense_physical_L':True})
        for cut in ['nonlinear','zero']:summary['cases'].append(one_case(n,cut,B,T,K,G,assembly))
        del B,T,K,G
    require(len(summary['cases'])==6,'Exactly six fixed cases required')
    require(all(case['status']!='FAILED_PRESERVED' for case in summary['cases']),'Actual case-integrity failure preserved')
    summary['status']='SIX_FIXED_FINITE_DIAGNOSTICS_RECORDED_NOT_A_CERTIFICATE'
except Exception:summary['failure']=traceback.format_exc();(E/'failure.txt').write_text(summary['failure'],encoding='utf-8')
finally:
    summary['finished_at']=utc();dump(E/'report.json',summary)
    manifest=[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(E.rglob('*')) if p.is_file()]
    dump(E/'manifest.json',manifest)
    with zipfile.ZipFile(ZIP,'x',zipfile.ZIP_DEFLATED) as z:
        for p in sorted(E.rglob('*')):
            if p.is_file():z.write(p,p.relative_to(ROOT).as_posix())
print(json.dumps({'status':summary['status'],'archive':str(ZIP),'archive_sha256':hashlib.sha256(ZIP.read_bytes()).hexdigest(),'archive_bytes':ZIP.stat().st_size}),flush=True)
if summary['status']=='FAILED_PRESERVED':raise RuntimeError('277 diagnostic failure retained without parameter adaptation')
