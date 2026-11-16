# 348F only: Linux atomic no-clobber rename of closed, validated child status.
import ctypes, errno, re, tempfile
SENTINEL_SOURCE = r'''
import ctypes, os, re
from pathlib import Path

def publish_exit(prefix, actual, before_publish=None):
    if type(actual) is not int: raise ValueError('Actual integer child exit required')
    temporary=prefix.with_suffix('.exit.tmp'); final=prefix.with_suffix('.exit')
    if final.exists() or final.is_symlink(): raise FileExistsError(final)
    with temporary.open('x',encoding='ascii',newline='\n') as stream:
        stream.write(str(actual)+'\n');stream.flush();os.fsync(stream.fileno())
    raw=temporary.read_bytes()
    if re.fullmatch(rb'-?[0-9]+\n',raw) is None or int(raw)!=actual:
        raise ValueError('Closed child exit sentinel differs')
    if before_publish is not None: before_publish()
    libc=ctypes.CDLL(None,use_errno=True)
    rename=libc.renameat2
    rename.argtypes=[ctypes.c_int,ctypes.c_char_p,ctypes.c_int,ctypes.c_char_p,ctypes.c_uint]
    rename.restype=ctypes.c_int
    if rename(-100,os.fsencode(temporary),-100,os.fsencode(final),1)!=0:
        code=ctypes.get_errno();raise OSError(code,os.strerror(code),str(final))
    if final.read_bytes()!=raw or temporary.exists(): raise ValueError('Published sentinel readback')
'''
exec(SENTINEL_SOURCE)
SENTINEL_TESTS = r'''
import json, tempfile
from pathlib import Path
checks=[]
def require_check(ok,label):
    if not ok:raise ValueError(label)
    checks.append(label)
with tempfile.TemporaryDirectory() as folder:
    root=Path(folder)
    p=root/'successful';publish_exit(p,0)
    require_check(p.with_suffix('.exit').read_bytes()==b'0\n','successful-zero')
    p=root/'failed';publish_exit(p,7)
    require_check(p.with_suffix('.exit').read_bytes()==b'7\n','nonzero-retained')
    try:publish_exit(p,0)
    except FileExistsError:pass
    else:raise ValueError('Duplicate final accepted')
    require_check(p.with_suffix('.exit').read_bytes()==b'7\n','duplicate-preserved')
    p=root/'interrupted'
    def interrupt():raise RuntimeError('deliberate prepublication interruption')
    try:publish_exit(p,0,interrupt)
    except RuntimeError:pass
    else:raise ValueError('Interruption absent')
    require_check(not p.with_suffix('.exit').exists() and p.with_suffix('.exit.tmp').read_bytes()==b'0\n','interrupted-not-published')
    p=root/'racing'
    def race():p.with_suffix('.exit').write_bytes(b'9\n')
    try:publish_exit(p,0,race)
    except FileExistsError:pass
    else:raise ValueError('Racing destination overwritten')
    require_check(p.with_suffix('.exit').read_bytes()==b'9\n','racing-destination-preserved')
    p=root/'boolean'
    try:publish_exit(p,False)
    except ValueError:pass
    else:raise ValueError('Boolean accepted')
    require_check(not p.with_suffix('.exit').exists(),'boolean-rejected')
if len(checks)!=6:raise ValueError('Sentinel regression count')
print(json.dumps({'sentinel_regressions':checks,'count':len(checks)}))
'''
import signal, time, resource, traceback
def observed_child(label,argv,timeout):
    require(platform.node()==OWNED_RUNTIME_NODE, 'Owned validation runtime changed')
    prefix=ROOT/label
    observation={'argv':argv,'hostname':platform.node(),'started_at':datetime.now(timezone.utc).isoformat(),
                 'actual_exit':None,'timed_out':False,'error':None}
    child=None;start=time.perf_counter()
    try:
        with prefix.with_suffix('.stdout').open('xb') as out, prefix.with_suffix('.stderr').open('xb') as err:
            child=subprocess.Popen(argv,cwd=ROOT,stdout=out,stderr=err,start_new_session=True)
            try: observation['actual_exit']=child.wait(timeout=timeout)
            except subprocess.TimeoutExpired:
                observation['timed_out']=True
                try: os.killpg(child.pid,signal.SIGKILL)
                except ProcessLookupError: pass
                observation['actual_exit']=child.wait()
            out.flush();os.fsync(out.fileno());err.flush();os.fsync(err.fileno())
    except BaseException:
        observation['error']=traceback.format_exc()
        if child is not None and child.poll() is None:
            try: os.killpg(child.pid,signal.SIGKILL)
            except ProcessLookupError: pass
            observation['actual_exit']=child.wait()
        raise
    finally:
        observation.update(finished_at=datetime.now(timezone.utc).isoformat(),wall_seconds=time.perf_counter()-start,
                           children_max_rss_kib_cumulative=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
        if observation['actual_exit'] is not None:
            publish_exit(prefix,observation['actual_exit'])
        observation['files']={ext:{'bytes':prefix.with_suffix(ext).stat().st_size,'sha256':digest(prefix.with_suffix(ext).read_bytes())}
                              for ext in ('.stdout','.stderr','.exit') if prefix.with_suffix(ext).is_file()}
        with prefix.with_suffix('.observation.json').open('x',encoding='utf-8') as stream:
            json.dump(observation,stream,indent=2);stream.write('\n')
        print(json.dumps(observation))
    return observation
for sentinel_mode,sentinel_args in [('normal',[]),('optimized',['-O'])]:
    sentinel=observed_child('sentinel-'+sentinel_mode,[sys.executable,*sentinel_args,'-c',SENTINEL_SOURCE+'\n'+SENTINEL_TESTS],30)
    require(sentinel['actual_exit']==0 and not sentinel['timed_out'] and sentinel['error'] is None,'Actual sentinel regressions failed')
    sentinel_result=json.loads((ROOT/('sentinel-'+sentinel_mode+'.stdout')).read_bytes())
    require(sentinel_result['count']==6 and len(set(sentinel_result['sentinel_regressions']))==6,'Six actual sentinel regressions required')
preflight=observed_child('preflight-call',[sys.executable,str(ROOT/'run_preflight348E.py')],300)
require(preflight['actual_exit']==0 and not preflight['timed_out'] and preflight['error'] is None,
        'Current 348E predicates failed: preserve files, stop actual validation, export evidence')
