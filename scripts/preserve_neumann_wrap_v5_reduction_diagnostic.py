"""Verify exact instrumentation archive; never a mathematical PASS."""
import hashlib,json,sys
from pathlib import Path
from verify_neumann_counting_reflection_diagnostic_v2 import unpack
def sha(b): return hashlib.sha256(b).hexdigest()
a=Path(sys.argv[1]); dest=Path(sys.argv[2])
b=a.read_bytes()
assert len(b)<4*2**20 and sha(b)=='d46074382c22937571863824a532b4f4c4878ed5ff2a4faec21ec4c8a1465f95'
raw=unpack(b); prefix='neumann-wrap-v5-reduction-diagnostic/'
assert set(raw)=={prefix+n for n in ('source.lean','runner.py','diagnostics.log','result.json')}
f={n[len(prefix):]:v for n,v in raw.items()}
assert sha(f['source.lean'])=='7a9fcb8095e15c3adb3eb50d85cd76ebe65809e5740f14c327aac41d93dbfe76'
assert sha(f['runner.py'])=='b917cc2dbfb8f504eff7c1b80bfb3ec7a9e11a01a07ec23ad51082f606ea5a03'
r=json.loads(f['result.json'])
assert r['source']=='b5baabdeba5951c7b25fc6b942676f5d2c0fc6b8'
assert r['command']==['lake','env','lean','-Ddiagnostics=true','tmp/neumann-rectangle-wrap-probe-hot-v5/NeumannRectangleWrapProbeDraft.lean']
assert r['cwd']=='/content/hrpoly-neumann-internal-bond-stencil-promoted-cold-v1'
assert r['exit']==1 and r['timed_out'] is False and r['timeout_seconds']==30 and 0<r['seconds']<30
assert sha(f['diagnostics.log'])==r['log_sha256']
assert r['scope']=='instrumentation only; no proof verdict'
report=dict(status='VERIFIED_DIAGNOSTIC_ONLY',archive_sha256=sha(b),record=r)
payload=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
assert not dest.exists()
dest.mkdir()
(dest/a.name).write_bytes(b)
for n,v in f.items(): (dest/n).write_bytes(v)
(dest/'independent-verification.json').write_bytes(payload)
print(payload.decode())
print('REPORT_SHA256='+sha(payload))
