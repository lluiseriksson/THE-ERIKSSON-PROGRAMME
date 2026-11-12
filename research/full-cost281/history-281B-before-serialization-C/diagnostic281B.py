"""Bounded whole-coexact 279/280 floating diagnostic. Linux own Colab ONLY.
Fabrication, not a proof, source audit, grade, gap or novelty claim.
"""
import os,sys,json,hashlib,traceback,zipfile,platform,io,contextlib
from pathlib import Path
from datetime import datetime,timezone
import numpy as np
import scipy
import scipy.linalg as la
import scipy.sparse as sp
import importlib.metadata as metadata

BASE='4ba7c61adb94d80f4cb985ab78e84d8346171b02'
ROOT=Path('/content/tep281-diagnostic');E=ROOT/'evidence'
ZIP=Path('/content/tep281-diagnostic-results.zip')
TOL=1e-8;REL=1e-10

def utc():return datetime.now(timezone.utc).isoformat()
def require(ok,msg):
    if not ok:raise ValueError(msg)
def finite(a,name):require(bool(np.all(np.isfinite(a))),name+' contains nonfinite entries')
def dump(p,obj):
    with p.open('x',encoding='utf-8',newline='\n') as f:
        json.dump(obj,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
def save(p,a):
    finite(a,p.name)
    with p.open('xb') as f:np.save(f,a,allow_pickle=False);f.flush();os.fsync(f.fileno())
def relative(a,b):return float(la.norm(a-b))/max(1.0,float(la.norm(a)),float(la.norm(b)))
def matrix_relative(a,b):return float(la.norm(a-b))/max(np.finfo(float).tiny,float(la.norm(a)),float(la.norm(b)))
def check(value,label):require(np.isfinite(value) and value<=TOL,label+' residual '+repr(value))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def cells(n):
    result=[]
    for i in range(n):
        t=(2*i*i)%n
        for I in (list(range(t)),[t],list(range(t+1,n))):
            if not I:continue
            for J in ([0],list(range(1,n))):
                for r in range(3):result.append((i,I,J,r))
    return result

def physical_rows(u,labels):
    n=u.shape[0];return np.array([np.sum(u[i,np.array(I)[:,None],np.array(J)[None,:],r])/np.sqrt(n**3*len(I)*len(J)) for i,I,J,r in labels])

def physical_energy(u,channel):
    n=u.shape[0];parity=np.indices((n,n,n)).sum(axis=0)%2
    weights=np.where(parity==(1 if channel==1 else 0),float(n*n),1/48)
    return float(sum(np.sum(weights[...,None]*np.abs(np.roll(u,-1,axis=j)-u)**2) for j in range(3)))

def physical_integrity(u,channel,labels,recorded_energy=None):
    n=u.shape[0];finite(u,'field');norm=float(np.vdot(u,u).real);require(norm>0,'Nonzero field required')
    energy=physical_energy(u,channel);mean=np.sum(u,axis=(0,1,2))
    div=sum(np.roll(u[...,j],1,axis=j)-u[...,j] for j in range(3))
    uh=np.fft.fftn(u,axes=(0,1,2),norm='ortho');grid=np.indices((n,n,n));g=np.exp(2j*np.pi*grid/n)-1
    D=np.sum(np.abs(g)**2,axis=0);den=np.where(D>0,D,1)
    pre=np.stack([(g[j]*uh[...,l]-g[l]*uh[...,j])/den for j,l in ((0,1),(0,2),(1,2))],axis=-1)
    rec=np.zeros_like(uh)
    for t,(j,l) in enumerate(((0,1),(0,2),(1,2))):rec[...,l]+=np.conj(g[j])*pre[...,t];rec[...,j]-=np.conj(g[l])*pre[...,t]
    row=physical_rows(u,labels)
    vals={'backward_divergence_scaled':float(la.norm(div.ravel()))/max(1.,np.sqrt(norm)),
          'global_mean_scaled':float(la.norm(mean))/max(1.,np.sqrt(n**3*norm)),
          'curl_adjoint_preimage_reconstruction_scaled':relative(rec,uh),
          'original_C_scaled':float(la.norm(row))/max(1.,np.sqrt(norm)),
          'recorded_energy_scaled':0.0 if recorded_energy is None else abs(energy-recorded_energy)/max(1.,abs(energy),abs(recorded_energy))}
    finite(pre,'curl preimage');finite(row,'original C rows')
    return {'norm_squared':norm,'physical_Q':energy,'physical_Rayleigh':energy/norm,'checks':vals},pre,row

def validate_record(u,channel,labels,recorded):
    report,_,_=physical_integrity(u,channel,labels,recorded)
    # Mutation tests exercise real integrity predicates, but intentionally do not
    # require C=0: the deterministic test curl need not be invisible.
    for key in ('global_mean_scaled','backward_divergence_scaled','curl_adjoint_preimage_reconstruction_scaled','recorded_energy_scaled'):check(report['checks'][key],key)
    return report

def blocks(n,channel,labels,directory):
    A=(n*n+1/48)/2;B=(n*n-1/48)/2;eps=-1 if channel==1 else 1
    q=np.array([n//2]*3);seen=set();parts=[];lams=[];explicit=[];columns=[];audit=[]
    # Each item stores only two 3xd Fourier coefficient matrices, never an
    # ambient dense (3n^3)^2 operator or whole physical U basis.
    def frame(k):
        if not any(k):return np.empty((3,0),complex)
        g=np.exp(2j*np.pi*np.array(k)/n)-1
        return la.null_space(np.conj(g)[None,:],rcond=REL)
    for k in np.ndindex(n,n,n):
        if k in seen:continue
        h=tuple((np.array(k)+q)%n);seen.update((k,h));F0=frame(k);F1=frame(h)
        g=np.exp(2j*np.pi*np.array(k)/n)-1;gh=np.exp(2j*np.pi*np.array(h)/n)-1
        D=float(np.vdot(g,g).real);Dh=float(np.vdot(gh,gh).real);gamma=np.vdot(g,gh)
        d0=F0.shape[1];d1=F1.shape[1]
        K=np.zeros((d0+d1,d0+d1),complex);K[:d0,:d0]=A*D*np.eye(d0);K[d0:,d0:]=A*Dh*np.eye(d1)
        K[:d0,d0:]=eps*B*gamma*(F0.conj().T@F1);K[d0:,:d0]=K[:d0,d0:].conj().T
        check(relative(K,K.conj().T),'Hermitian compressed block')
        val,V=la.eigh(K,check_finite=True);T0=F0@V[:d0,:];T1=F1@V[d0:,:]
        if d0==0 or d1==0:pred=np.array([12*A]*2)
        else:
            r1=np.sqrt(A*A*(D-6)**2+B*B*abs(gamma)**2)
            r2=np.sqrt(A*A*(D-6)**2+B*B*abs(gamma)**4/(D*Dh))
            pred=np.sort([6*A-r1,6*A+r1,6*A-r2,6*A+r2])
        err=relative(val,pred);check(err,'279 all polarizations explicit roots')
        off=len(lams);lams.extend(val.tolist());explicit.extend(pred.tolist());parts.append((k,h,T0,T1,off,len(val)))
        # Exact original unitary Fourier rows, with both pair frequencies.
        R=np.empty((len(labels),len(val)),complex)
        for row,(i,I,J,r) in enumerate(labels):
            def factor(freq):return np.exp(2j*np.pi*freq[0]*i/n)*sum(np.exp(2j*np.pi*freq[1]*j/n) for j in I)*sum(np.exp(2j*np.pi*freq[2]*j/n) for j in J)/(n**3*np.sqrt(len(I)*len(J)))
            R[row]=factor(k)*T0[r]+factor(h)*T1[r]
        columns.append(R);audit.append({'k':list(k),'h':list(h),'frame_dimensions':[d0,d1],'eigenvalues':val.tolist(),'279_explicit':pred.tolist(),'relative_root_residual':err})
    lam=np.array(lams);C=np.concatenate(columns,axis=1);finite(lam,'full eigenvalues');finite(C,'full original C')
    require(len(lam)==2*(n**3-1),'Whole actual per-channel dimension differs')
    low=np.flatnonzero(lam<1);high=np.flatnonzero(lam>1)
    require(len(low)+len(high)==len(lam),'Threshold eigenvalue exactly1 requires explicit resolution')
    require(len(low)==n-2,'279 per-channel low multiplicity differs')
    require(float(np.max(lam[low]))<=1/8+TOL and float(np.min(lam[high]))>=16/3-TOL,'279 low/high separation differs')
    dump(directory/'blocks.json',audit);save(directory/'all-eigenvalues.npy',lam);save(directory/'279-explicit-eigenvalues.npy',np.array(explicit));save(directory/'C-in-full-spectral-basis.npy',C)
    # Full eigencoordinates are retained: reproducibility does not rely on an
    # unspecified SVD/eigh phase or repeated-root orientation.
    save(directory/'pair-frequencies.npy',np.array([[k,h] for k,h,_,_,_,_ in parts],dtype=int))
    save(directory/'pair-column-offsets.npy',np.array([[off,d] for _,_,_,_,off,d in parts],dtype=int))
    save(directory/'pair-Fourier-eigenvectors.npy',np.concatenate([np.vstack((T0,T1)) for _,_,T0,T1,_,_ in parts],axis=1))
    return lam,C,parts,low,high

def field_from_coeff(n,parts,coeff):
    uh=np.zeros((n,n,n,3),complex)
    for k,h,T0,T1,off,d in parts:uh[k]+=T0@coeff[off:off+d];uh[h]+=T1@coeff[off:off+d]
    return np.fft.ifftn(uh,axes=(0,1,2),norm='ortho')

def independent_n4(channel,labels,lam,C,directory):
    n=4;v=n**3;coords=np.arange(v).reshape(n,n,n);Ds=[]
    for j in range(3):
        nexts=np.roll(coords,-1,axis=j).ravel();Ds.append(sp.csr_matrix((np.tile([-1.,1.],v),(np.repeat(np.arange(v),2),np.column_stack((np.arange(v),nexts)).ravel())),shape=(v,v)).toarray())
    z=np.zeros((v,v));D0,D1,D2=Ds
    curl=np.block([[-D1,D0,z],[-D2,z,D0],[z,-D2,D1]])
    adj=curl.T;U,s,_=la.svd(adj,full_matrices=False,check_finite=True,lapack_driver='gesvd');cut=REL*float(s[0]);rank=int(np.sum(s>cut));U=U[:,:rank]
    parity=np.indices((n,n,n)).sum(axis=0).ravel()%2;w=np.where(parity==(1 if channel==1 else 0),n*n,1/48)
    K=np.zeros((rank,rank))
    for D in Ds:
        for r in range(3):DU=D@U[r*v:(r+1)*v];K+=DU.T@(w[:,None]*DU)
    vals=la.eigvalsh((K+K.T)/2);cmp=relative(vals,np.sort(lam));check(cmp,'Independent physical curl-image full spectrum')
    Cphys=np.zeros((len(labels),3*v))
    for row,(i,I,J,r) in enumerate(labels):Cphys[row,r*v+coords[i,np.array(I)[:,None],np.array(J)[None,:]].ravel()]=1/np.sqrt(v*len(I)*len(J))
    CU=Cphys@U;gram=matrix_relative(CU@CU.T,C@C.conj().T);check(gram,'Independent physical C_U row Gram')
    _,sr,Vh=la.svd(CU,full_matrices=True,check_finite=True,lapack_driver='gesvd');rcut=REL*float(sr[0]);rrank=int(np.sum(sr>rcut));Z=Vh[rrank:].T
    require(Z.shape[1]>0,'Independent n4 numerical invisible kernel empty')
    reduced=Z.T@K@Z;ev,vec=la.eigh((reduced+reduced.T)/2,subset_by_index=[0,0],check_finite=True)
    u=(U@Z@vec[:,0]).reshape(3,n,n,n).transpose(1,2,3,0)
    integrity,pre,row=physical_integrity(u,channel,labels,float(ev[0]));save(directory/'n4-independent-kernel-witness.npy',u);save(directory/'n4-independent-curl-preimage.npy',pre)
    for key,value in integrity['checks'].items():check(value,'Independent n4 '+key)
    save(directory/'n4-physical-coexact-eigenvalues.npy',vals);save(directory/'n4-curl-adjoint-singular-values.npy',s);save(directory/'n4-CU-singular-values.npy',sr)
    return {'method':'Independent real physical forward-curl adjoint SVD image; physical weighted differences; original spatial cells','curl_rank_diagnostic':rank,'curl_relative_cutoff':REL,'curl_absolute_cutoff':cut,'dimension_expected':2*(v-1),'full_spectrum_relative_residual':cmp,'original_C_U_rowGram_relative_residual':gram,'C_U_numerical_rank':rrank,'C_U_absolute_cutoff':rcut,'C_U_nullity':int(Z.shape[1]),'direct_kernel_minimum':float(ev[0]),'direct_kernel_witness':integrity}

def one_case(n,channel):
    directory=E/('n%d-channel%d'%(n,channel));directory.mkdir();r={'n':n,'channel':channel,'H':n*n,'a':1/48,'c':1,'tau':[(2*i*i)%n for i in range(n)],'status':'FAILED_PRESERVED','started_at':utc()}
    try:
        labels=cells(n);dump(directory/'original-row-labels.json',[{'i':i,'I':I,'J':J,'component':j,'channel':channel} for i,I,J,j in labels]);lam,C,parts,L,F=blocks(n,channel,labels,directory)
        CL=C[:,L];CF=C[:,F];DL=1-lam[L];BF=lam[F]-1;M=(CF/BF[None,:])@CF.conj().T
        herm=matrix_relative(M,M.conj().T);check(herm,'Shifted high-response Hermitian');M=(M+M.conj().T)/2
        mu,W=la.eigh(M,check_finite=True);finite(mu,'M eigenvalues');cut=REL*float(np.max(np.abs(mu)));keep=mu>cut
        require(float(mu[0])>=-TOL*max(1.,float(np.max(mu))),'M materially negative')
        Winv=W[:,keep]/np.sqrt(mu[keep])[None,:];Mdag=Winv@Winv.conj().T;range_res=matrix_relative(M@Mdag@CL,CL)
        cost=CL.conj().T@Mdag@CL;eta=cost/np.sqrt(DL[:,None]*DL[None,:]);eta=(eta+eta.conj().T)/2;etas,V=la.eigh(eta,check_finite=True)
        coeff=np.zeros(len(lam),complex);coeff[L]=V[:,0]/np.sqrt(DL);y=CL@coeff[L];coeff[F]=-(CF.conj().T@(Mdag@y))/BF
        u=field_from_coeff(n,parts,coeff);originalQ=physical_energy(u,channel);predQ=float(np.sum(lam*np.abs(coeff)**2));prednorm=float(np.vdot(coeff,coeff).real)
        info,pre,row=physical_integrity(u,channel,labels,predQ)
        checks={'spectral_physical_Q':abs(originalQ-predQ)/max(1.,abs(originalQ),abs(predQ)),'spectral_physical_norm':abs(info['norm_squared']-prednorm)/max(1.,prednorm),'original_rows_vs_unitary_rows':relative(row,C@coeff),'range_CL_in_M':range_res}
        save(directory/'shifted-high-response-M.npy',M);save(directory/'M-all-eigenvalues.npy',mu);save(directory/'M-discarded-eigenvalues.npy',mu[~keep]);save(directory/'M-pseudoinverse.npy',Mdag);save(directory/'eta-matrix.npy',eta);save(directory/'eta-all-eigenvalues.npy',etas);save(directory/'lowest-shifted-cost-full-coefficients.npy',coeff);save(directory/'complex-field.npy',u);save(directory/'complex-curl-preimage-fft.npy',pre);save(directory/'complex-original-C.npy',row)
        r.update(original_rows=len(labels),whole_per_channel_dimension=len(lam),low_dimension=len(L),high_dimension=len(F),low_eigenvalues=lam[L].tolist(),high_min=float(np.min(lam[F])),M={'relative_cutoff':REL,'absolute_cutoff':cut,'numerical_rank':int(np.sum(keep)),'all_eigenvalues':mu.tolist(),'discarded_eigenvalues':mu[~keep].tolist(),'range_residual':range_res,'rank_status':'Floating cutoff diagnostic only; no exact rank certificate'},eta_eigenvalues=etas.tolist(),eta_min=float(etas[0]),eta_meaning='Eigenvalue of D_L^-1/2 C_L* Mdag C_L D_L^-1/2; NOT a physical Rayleigh quotient',complex_witness=info,assembly_checks=checks)
        components=[];eligibility=1e-12*info['norm_squared']
        r['real_component_original_norm_squared_eligibility_threshold']=eligibility
        r['real_component_policy']='Fixed relative norm cutoff1e-12; normalize every eligible component to unit counting norm, then require actual original-field integrity before selecting. Preserve original and normalized vectors.'
        for name,v in [('real',u.real),('imaginary',u.imag)]:
            vn=float(np.vdot(v,v).real);save(directory/(name+'-field.npy'),v)
            if vn<eligibility or vn<=np.finfo(float).tiny:components.append({'name':name,'original_norm_squared':vn,'eligible':False,'reason':'Below fixed relative component-size cutoff'});continue
            normalized=v/np.sqrt(vn);save(directory/(name+'-normalized-field.npy'),normalized)
            vi,vp,vr=physical_integrity(normalized,channel,labels);save(directory/(name+'-curl-preimage-fft.npy'),vp);save(directory/(name+'-original-C.npy'),vr)
            valid=all(np.isfinite(value) and value<=TOL for value in vi['checks'].values())
            components.append({'name':name,'original_norm_squared':vn,'eligible':True,'normalized_integrity_valid':bool(valid),**vi})
        candidates=[x for x in components if x['eligible'] and x['normalized_integrity_valid']];require(bool(candidates),'No eligible normalized real component passes original physical integrity; candidate ambiguous/failing and retained');chosen=min(candidates,key=lambda x:x['physical_Rayleigh'])
        r['real_components']=components;r['selected_real_component']=chosen['name'];r['selected_real_Rayleigh']=chosen['physical_Rayleigh']
        r['below_one_finite_witness_integrity_verified']=bool(chosen['physical_Rayleigh']<1 and all(np.isfinite(v) and v<=TOL for v in chosen['checks'].values()) and all(np.isfinite(v) and v<=TOL for v in checks.values()))
        if n==4:r['independent_n4']=independent_n4(channel,labels,lam,C,directory)
        # Preserve all candidate vectors and measured failures BEFORE raising.
        dump(directory/'pre-acceptance-measurements.json',r)
        for key,value in checks.items():check(value,key)
        for key,value in info['checks'].items():check(value,'complex '+key)
        for key,value in chosen['checks'].items():check(value,'selected real '+key)
        r['status']='FIXED_FINITE_FLOATING_DIAGNOSTIC_RECORDED'
    except Exception:r['failure']=traceback.format_exc();(directory/'failure.txt').write_text(r['failure'],encoding='utf-8')
    finally:r['finished_at']=utc();dump(directory/'case.json',r)
    print(json.dumps({'n':n,'channel':channel,'status':r['status'],'eta_min':r.get('eta_min'),'actual_real_Rayleigh':r.get('selected_real_Rayleigh')},allow_nan=False),flush=True)
    return r

def mutation_mode():
    # Tiny n4 deterministic physical curl, no spectral sweep or cost solve.
    n=4;grid=np.indices((n,n,n));p=np.sin(2*np.pi*grid[0]/n)*np.cos(2*np.pi*grid[1]/n)
    u=np.zeros((n,n,n,3));u[...,0]=-(np.roll(p,1,axis=1)-p);u[...,1]=np.roll(p,1,axis=0)-p
    labels=cells(n);q=physical_energy(u,1);validate_record(u,1,labels,q);out={'schema':'TEP281-MUTATION-1','optimized':not __debug__,'source_sha256':sha(Path(__file__)),'original_record_accepted':True,'results':[]}
    for name,v,energy in [('changed_recorded_energy',u,q+max(1.,abs(q))),('added_harmonic_constant',u+np.array([1.,0.,0.]),q)]:
        try:validate_record(v,1,labels,energy);out['results'].append({'mutation':name,'rejected':False})
        except ValueError as exc:out['results'].append({'mutation':name,'rejected':True,'reason':str(exc)})
    print(json.dumps(out,allow_nan=False),flush=True);require(all(x['rejected'] for x in out['results']),'Mutation escaped real integrity predicates')

def main():
    require(os.name=='posix' and Path('/content').is_dir(),'Own Linux Colab only; never local Windows math')
    if sys.argv[1:]==['--mutations-only']:mutation_mode();return
    require(not sys.argv[1:],'No adaptation/options accepted for fixed six cases')
    require(not ROOT.exists() and not ZIP.exists(),'Fresh owned281 roots required');E.mkdir(parents=True)
    report={'schema':'TEP281-FULL-COST-1','construction_base':BASE,'script_raw_sha256':sha(Path(__file__)),'started_at':utc(),'fixed_n':[4,8,16],'channels':[1,2],'cut':'2i^2 mod n','relative_pseudoinverse_cutoff':REL,'integrity_tolerance':TOL,'status':'FAILED_PRESERVED','cases':[],'billing_units':None,'independent_provider_replication':False,'limitations':'Selected finite classical floating-point exploration only. Numerical ranks, no exact rank certificate, no all-n/gap/novelty or continuum conclusion. Eta is not Rayleigh. Actual elapsed runtime is not a billed quantity.'}
    try:
        shutil_source=E/'diagnostic281B.py';shutil_source.write_bytes(Path(__file__).read_bytes())
        dump(E/'native-environment.json',{'python':sys.version,'platform':platform.platform(),'numpy':np.__version__,'scipy':scipy.__version__,'packages':{name:{'path':str(Path(module.__file__)),'sha256':sha(Path(module.__file__))} for name,module in [('numpy',np),('scipy',scipy)]},'thread_environment':{key:os.environ.get(key) for key in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS']}})
        package_files=[]
        for name in ('numpy','scipy'):
            distribution=metadata.distribution(name)
            for item in sorted(distribution.files or [],key=str):
                if str(item).endswith(('.so','.pyd','/RECORD','/METADATA')):
                    physical=Path(distribution.locate_file(item))
                    if physical.is_file():package_files.append({'distribution':name,'version':distribution.version,'relative_file':str(item),'bytes':physical.stat().st_size,'sha256':sha(physical)})
        dump(E/'package-native-file-hashes.json',{'meaning':'Actual native extension and distribution RECORD/METADATA bytes; provenance capture, not an authenticity certification or package lock','files':package_files})
        config=io.StringIO()
        with contextlib.redirect_stdout(config):np.show_config();scipy.show_config()
        (E/'native-build-config.txt').write_text(config.getvalue(),encoding='utf-8')
        for n in (4,8,16):
            for channel in (1,2):report['cases'].append(one_case(n,channel))
        require(len(report['cases'])==6 and all(x['status']=='FIXED_FINITE_FLOATING_DIAGNOSTIC_RECORDED' for x in report['cases']),'Actual fixed-case integrity failure preserved')
        report['status']='SIX_WHOLE_COEXACT_FINITE_DIAGNOSTICS_RECORDED_NOT_A_CERTIFICATE'
    except Exception:report['failure']=traceback.format_exc();(E/'failure.txt').write_text(report['failure'],encoding='utf-8')
    finally:
        report['finished_at']=utc();dump(E/'report.json',report)
        dump(E/'manifest.json',[{'path':p.relative_to(ROOT).as_posix(),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(E.rglob('*')) if p.is_file()])
        with zipfile.ZipFile(ZIP,'x',zipfile.ZIP_DEFLATED) as z:
            for p in sorted(E.rglob('*')):
                if p.is_file():z.write(p,p.relative_to(ROOT).as_posix())
    print(json.dumps({'status':report['status'],'archive':str(ZIP),'sha256':sha(ZIP),'bytes':ZIP.stat().st_size}),flush=True)
    require(report['status']!='FAILED_PRESERVED','Actual diagnostic failure retained; no adaptive sweep')

if __name__=='__main__':main()
