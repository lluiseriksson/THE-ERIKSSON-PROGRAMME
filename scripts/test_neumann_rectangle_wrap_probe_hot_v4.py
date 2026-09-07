"""Exact bounded v4 instrumentation delta; no Lean/network."""
import ast, hashlib, runpy, subprocess
from pathlib import Path
runpy.run_path('scripts/test_neumann_rectangle_wrap_probe_hot_actual.py',run_name='__main__')
old='70072b776d85c42e5f5935160c885b2b24fe3431'
new='d6e06209b85bf31c82095a51fc22f1aa59593ed6'
def blob(ref,path):
    return subprocess.check_output(['git','cat-file','blob',ref+':'+path],timeout=5)
def norm(s):
    return ast.dump(ast.parse(s))
p='tmp/NeumannRectangleWrapProbeDraft.lean'
b=blob(new,p)
assert hashlib.sha256(b).hexdigest()=='4af75143ea217d790c207a5eb6a120963e842efd688850dac0f9be7f31f810d1'
def statement(s):
    return s.split('theorem neumannRectangle_siteFit_retains_wrapBond :',1)[1].split(' := by',1)[0]
assert statement(blob(old,p).decode())==statement(b.decode())
assert 'maxRecDepth' not in b.decode() and 'maxHeartbeats' not in b.decode()
r=Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v2.py').read_text().replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v2','neumann-rectangle-wrap-probe-hot-v4').replace('c7e713335bef48fdca25cc332e3fa241d3fb509e5eca5038daa1c64cafbc9ee8','4af75143ea217d790c207a5eb6a120963e842efd688850dac0f9be7f31f810d1')
assert norm(r)==norm(Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v4.py').read_text())
v=Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v2.py').read_text().replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v2','neumann-rectangle-wrap-probe-hot-v4').replace('8d9703f5caeb3b621e217989c3a88ee94588277eb4bce447282c21309cbc161f','1f3ffb0cd64667a9c2e971d5c7ea07e190d812bc408c63ff1b1e95f8c0229e10')
assert norm(v)==norm(Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v4.py').read_text())
assert hashlib.sha256(blob('','scripts/colab_neumann_rectangle_wrap_probe_hot_v4.py')).hexdigest()=='1f3ffb0cd64667a9c2e971d5c7ea07e190d812bc408c63ff1b1e95f8c0229e10'
print('WRAP_V4_EXACT_DELTA_PASS COMPILER_CHECKED=0')
