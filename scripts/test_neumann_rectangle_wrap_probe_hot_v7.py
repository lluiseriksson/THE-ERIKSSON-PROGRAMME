"""Exact bounded v7 instrumentation delta; no Lean/network."""
import ast, hashlib, runpy, subprocess
from pathlib import Path
runpy.run_path('scripts/test_neumann_rectangle_wrap_probe_hot_actual.py',run_name='__main__')
old='70072b776d85c42e5f5935160c885b2b24fe3431'
new='baf5fa136663fe71a9cf07dacd4e365b0026942e'
def blob(ref,path):
    return subprocess.check_output(['git','cat-file','blob',ref+':'+path],timeout=5)
def norm(s):
    return ast.dump(ast.parse(s))
p='tmp/NeumannRectangleWrapProbeDraft.lean'
b=blob(new,p)
assert hashlib.sha256(b).hexdigest()=='9c117d3ebfd78648a3e0a07483618ce72cf3b93014217021a2e99b04bca9a447'
def statement(s):
    return s.split('theorem neumannRectangle_siteFit_retains_wrapBond :',1)[1].split(' := by',1)[0]
assert statement(blob(old,p).decode())==statement(b.decode())
assert 'maxRecDepth' not in b.decode() and 'maxHeartbeats' not in b.decode()
r=Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v2.py').read_text().replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v2','neumann-rectangle-wrap-probe-hot-v7').replace('c7e713335bef48fdca25cc332e3fa241d3fb509e5eca5038daa1c64cafbc9ee8','9c117d3ebfd78648a3e0a07483618ce72cf3b93014217021a2e99b04bca9a447')
assert norm(r)==norm(Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v7.py').read_text())
v=Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v2.py').read_text().replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v2','neumann-rectangle-wrap-probe-hot-v7').replace('8d9703f5caeb3b621e217989c3a88ee94588277eb4bce447282c21309cbc161f','fb4b4e608b10c95d3216bd7eb3da4c6ed168b2cf000de4e04bd4e6cc37a15320')
assert norm(v)==norm(Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v7.py').read_text())
assert hashlib.sha256(blob('','scripts/colab_neumann_rectangle_wrap_probe_hot_v7.py')).hexdigest()=='fb4b4e608b10c95d3216bd7eb3da4c6ed168b2cf000de4e04bd4e6cc37a15320'
print('WRAP_V7_EXACT_DELTA_PASS COMPILER_CHECKED=0')
