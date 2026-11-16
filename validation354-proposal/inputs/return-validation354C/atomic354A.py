"""Linux-only atomic no-clobber publication for actual exits and transported bytes."""
import os,re,ctypes,hashlib
from pathlib import Path
if os.name!='posix' or not Path('/content').is_dir(): raise RuntimeError('Own Colab only')
def require(ok,msg):
    if not ok: raise ValueError(msg)
def no_replace(temp,final):
    libc=ctypes.CDLL(None,use_errno=True);fn=libc.renameat2
    fn.argtypes=[ctypes.c_int,ctypes.c_char_p,ctypes.c_int,ctypes.c_char_p,ctypes.c_uint];fn.restype=ctypes.c_int
    if fn(-100,os.fsencode(temp),-100,os.fsencode(final),1)!=0:
        e=ctypes.get_errno();raise OSError(e,os.strerror(e),str(final))
def publish_bytes(final,raw,expected_bytes,expected_sha,before_publish=None):
    require(type(raw) is bytes and type(expected_bytes) is int and expected_bytes>=0,'Raw bytes/length types')
    require(len(raw)==expected_bytes and hashlib.sha256(raw).hexdigest()==expected_sha,'Hash before materialization')
    require(not final.exists() and not final.is_symlink(),'New destination')
    for p in final.parents: require(not p.is_symlink(),'Symlink parent')
    temp=final.with_name(final.name+'.tmp')
    with temp.open('xb') as f:
        f.write(raw);f.flush();os.fsync(f.fileno())
    require(temp.read_bytes()==raw,'Closed temporary readback')
    if before_publish is not None: before_publish()
    no_replace(temp,final)
    require(final.read_bytes()==raw and not temp.exists(),'Published readback')
    fd=os.open(final.parent,os.O_RDONLY|os.O_DIRECTORY)
    try:os.fsync(fd)
    finally:os.close(fd)
def publish_exit(prefix,actual,before_publish=None):
    require(type(actual) is int,'Actual integer exit, not bool')
    raw=(str(actual)+'\n').encode('ascii')
    publish_bytes(prefix.with_suffix('.exit'),raw,len(raw),hashlib.sha256(raw).hexdigest(),before_publish)
def read_exit(path,require_success=False):
    require(path.is_file() and not path.is_symlink(),'Missing or unsafe exit')
    raw=path.read_bytes();require(re.fullmatch(rb'-?[0-9]+\n',raw) is not None,'Malformed/empty exit')
    actual=int(raw)
    if require_success: require(raw==b'0\n','Native exit is not exact success')
    return actual
