# Prepared offline. Execute only in this chat's own Linux Colab CPU.
from pathlib import Path
from datetime import datetime,timezone
import subprocess,tempfile,hashlib,json,time,platform,resource,zipfile,base64
if platform.system()!='Linux':raise RuntimeError('Own Colab Linux required')
SHA='b9d9dfdee043a62ec5d30926e215f8a581507b70'
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic();root=Path(tempfile.mkdtemp(prefix='tep188-',dir='/content'));ev=root/'evidence';ev.mkdir()
report={'unit':188,'source_sha':SHA,'started_utc':start,'steps':[],'payloads':[],'billed_units':None,'execution_plane':'Own Colab Linux CPU'}
def run(args,label,cwd,timeout=180):
    t=time.monotonic();p=subprocess.Popen(args,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    try:out,err=p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:p.kill();out,err=p.communicate()
    (ev/(label+'.stdout.txt')).write_bytes(out);(ev/(label+'.stderr.txt')).write_bytes(err)
    tmp=ev/(label+'.exit.tmp');tmp.write_text(str(p.returncode)+'\n');tmp.replace(ev/(label+'.exit.txt'))
    report['steps'].append({'label':label,'actual_exit':p.returncode,'seconds':time.monotonic()-t})
    if p.returncode:raise RuntimeError(label+' failed; full logs retained')
    return out.decode().strip()
try:
    for name in ['fresh-a','fresh-b']:
        clone=root/name
        run(['git','clone','--filter=blob:none','--no-checkout','--depth','1','--branch','codex/tep-partial-invariance-20261107','https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git',str(clone)],name+'-clone',root)
        run(['git','sparse-checkout','set','--no-cone','/scripts/partial_invariance188.py','/papers/flat-coarse-rank/research/2026-11-07_partial-invariance188.txt','/papers/flat-coarse-rank/integrated-revision/revision187/sobolev.tex'],name+'-sparse',clone)
        run(['git','checkout','--detach',SHA],name+'-checkout',clone)
        actual=run(['git','rev-parse','HEAD'],name+'-head',clone)
        if actual!=SHA:raise ValueError('Wrong executed source')
        for mode,args in [('normal',['python3']),('optimized',['python3','-O'])]:
            run(args+['scripts/partial_invariance188.py'],name+'-'+mode,clone,180)
            payload=(clone/'payload188.json').read_bytes();obj=json.loads(payload)
            if obj['case_count']!=648 or obj['mutation_rejections']!=6 or obj['all_mutations_rejected'] is not True:raise ValueError('Invalid explicit acceptance counters')
            (ev/(name+'-'+mode+'-payload.json')).write_bytes(payload)
            report['payloads'].append({'clone':name,'mode':mode,'sha256':hashlib.sha256(payload).hexdigest(),'cases':obj['case_count'],'rejected_mutations':obj['mutation_rejections']})
        for rel in ['scripts/partial_invariance188.py','papers/flat-coarse-rank/research/2026-11-07_partial-invariance188.txt','papers/flat-coarse-rank/integrated-revision/revision187/sobolev.tex']:
            raw=(clone/rel).read_bytes();target=ev/(name+'-'+Path(rel).name);target.write_bytes(raw)
    if len({x['sha256'] for x in report['payloads']})!=1:raise ValueError('Fresh normal/optimized payload mismatch')
    report['status']='FINITE_DIAGNOSTICS_MATCHED_NOT_ALL_SIZE_PROOF'
except Exception:
    import traceback
    report['status']='FAILED_PRESERVED';(ev/'failure.txt').write_text(traceback.format_exc())
finally:
    report.update(finished_utc=datetime.now(timezone.utc).isoformat(),seconds=time.monotonic()-tick,child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    (ev/'report188.json').write_text(json.dumps(report,indent=2)+'\n')
    manifest=[{'path':p.name,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in sorted(ev.iterdir())]
    (ev/'manifest188.json').write_text(json.dumps(manifest,indent=2)+'\n')
    out=Path('/content/tep188-evidence.zip')
    with zipfile.ZipFile(out,'w',zipfile.ZIP_DEFLATED) as z:
        for p in sorted(ev.iterdir()):z.write(p,p.name)
    raw=out.read_bytes();print('REPORT188='+json.dumps(report));print('ZIP188_SHA256='+hashlib.sha256(raw).hexdigest()+' BYTES='+str(len(raw)));print('EXPORT188='+base64.b64encode(raw).decode())