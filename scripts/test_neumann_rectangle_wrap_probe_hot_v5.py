"""Exact bounded v5 instrumentation delta; no Lean/network."""
import ast, hashlib, runpy, subprocess
from pathlib import Path
runpy.run_path('scripts/test_neumann_rectangle_wrap_probe_hot_actual.py',run_name='__main__')
old='70072b776d85c42e5f5935160c885b2b24fe3431'
new='b5baabdeba5951c7b25fc6b942676f5d2c0fc6b8'
def blob(ref,path):
    return subprocess.check_output(['git','cat-file','blob',ref+':'+path],timeout=5)
def norm(s):
    return ast.dump(ast.parse(s))
p='tmp/NeumannRectangleWrapProbeDraft.lean'
b=blob(new,p)
assert hashlib.sha256(b).hexdigest()=='7a9fcb8095e15c3adb3eb50d85cd76ebe65809e5740f14c327aac41d93dbfe76'
def statement(s):
    return s.split('theorem neumannRectangle_siteFit_retains_wrapBond :',1)[1].split(' := by',1)[0]
assert statement(blob(old,p).decode())==statement(b.decode())
assert 'maxRecDepth' not in b.decode() and 'maxHeartbeats' not in b.decode()
r=Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v2.py').read_text().replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v2','neumann-rectangle-wrap-probe-hot-v5').replace('c7e713335bef48fdca25cc332e3fa241d3fb509e5eca5038daa1c64cafbc9ee8','7a9fcb8095e15c3adb3eb50d85cd76ebe65809e5740f14c327aac41d93dbfe76')
assert norm(r)==norm(Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v5.py').read_text())
v=Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v2.py').read_text().replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v2','neumann-rectangle-wrap-probe-hot-v5').replace('8d9703f5caeb3b621e217989c3a88ee94588277eb4bce447282c21309cbc161f','68fa6b862d08b99aa4ffdbce8eaf332dd9f34ef47d9ce0325d125653ed1b2135')
assert norm(v)==norm(Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v5.py').read_text())
assert hashlib.sha256(blob('','scripts/colab_neumann_rectangle_wrap_probe_hot_v5.py')).hexdigest()=='68fa6b862d08b99aa4ffdbce8eaf332dd9f34ef47d9ce0325d125653ed1b2135'
print('WRAP_V5_EXACT_DELTA_PASS COMPILER_CHECKED=0')
