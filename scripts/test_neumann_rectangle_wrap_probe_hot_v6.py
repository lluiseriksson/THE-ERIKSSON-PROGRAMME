"""Exact bounded v6 instrumentation delta; no Lean/network."""
import ast, hashlib, runpy, subprocess
from pathlib import Path
runpy.run_path('scripts/test_neumann_rectangle_wrap_probe_hot_actual.py',run_name='__main__')
old='70072b776d85c42e5f5935160c885b2b24fe3431'
new='64c45ebc65ed35ae4fac6a6287876aad25338e10'
def blob(ref,path):
    return subprocess.check_output(['git','cat-file','blob',ref+':'+path],timeout=5)
def norm(s):
    return ast.dump(ast.parse(s))
p='tmp/NeumannRectangleWrapProbeDraft.lean'
b=blob(new,p)
assert hashlib.sha256(b).hexdigest()=='83e025a945b1a11a2779c63eb65cd097e1b23892447cb132cde00a99876cb501'
def statement(s):
    return s.split('theorem neumannRectangle_siteFit_retains_wrapBond :',1)[1].split(' := by',1)[0]
assert statement(blob(old,p).decode())==statement(b.decode())
assert 'maxRecDepth' not in b.decode() and 'maxHeartbeats' not in b.decode()
r=Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v2.py').read_text().replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v2','neumann-rectangle-wrap-probe-hot-v6').replace('c7e713335bef48fdca25cc332e3fa241d3fb509e5eca5038daa1c64cafbc9ee8','83e025a945b1a11a2779c63eb65cd097e1b23892447cb132cde00a99876cb501')
assert norm(r)==norm(Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v6.py').read_text())
v=Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v2.py').read_text().replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v2','neumann-rectangle-wrap-probe-hot-v6').replace('8d9703f5caeb3b621e217989c3a88ee94588277eb4bce447282c21309cbc161f','4aa0f844f18e7bf081eef2086a9a9a9882539e9fa1fdf70f320fb17d00624d40')
assert norm(v)==norm(Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v6.py').read_text())
assert hashlib.sha256(blob('','scripts/colab_neumann_rectangle_wrap_probe_hot_v6.py')).hexdigest()=='4aa0f844f18e7bf081eef2086a9a9a9882539e9fa1fdf70f320fb17d00624d40'
print('WRAP_V6_EXACT_DELTA_PASS COMPILER_CHECKED=0')
