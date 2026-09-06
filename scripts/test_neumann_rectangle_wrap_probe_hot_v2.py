"""Exact v1-to-v2 instrumental delta, parent evidence and public statement. No Lean."""
import ast,hashlib,runpy,subprocess
from pathlib import Path
runpy.run_path('scripts/test_neumann_rectangle_wrap_probe_hot_actual.py',run_name='__main__')
def blob(ref,path):
    return subprocess.check_output(['git','cat-file','blob',ref+':'+path],timeout=5)
def norm(s):
    return ast.dump(ast.parse(s))
old='5442189556b1c85e3ac0cb864403cc65f8e23b31'
new='70072b776d85c42e5f5935160c885b2b24fe3431'
src='tmp/NeumannRectangleWrapProbeDraft.lean'
before=blob(old,src).decode()
after=blob(new,src).decode()
def statement(s):
    return s.split('theorem neumannRectangle_siteFit_retains_wrapBond :',1)[1].split(' := by',1)[0]
assert statement(before)==statement(after),'PUBLIC_WITNESS_CHANGED'
assert 'maxRecDepth' not in after and 'maxHeartbeats' not in after
assert hashlib.sha256(after.encode()).hexdigest()=='c7e713335bef48fdca25cc332e3fa241d3fb509e5eca5038daa1c64cafbc9ee8'
r0=Path('scripts/colab_neumann_rectangle_wrap_probe_hot.py').read_text()
r1=Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v2.py').read_text()
expected=r0.replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v1','neumann-rectangle-wrap-probe-hot-v2').replace(
'fd06be9b1c130fe4ba462ea5f4597794a8dfd9e49a303f8ee9dd6926882a4fa6','c7e713335bef48fdca25cc332e3fa241d3fb509e5eca5038daa1c64cafbc9ee8')
assert norm(expected)==norm(r1),'UNEXPECTED_RUNNER_DELTA'
rb=blob('76110785c5f4d186f6528dfb138d212d839c7a14','scripts/colab_neumann_rectangle_wrap_probe_hot_v2.py')
assert hashlib.sha256(rb).hexdigest()=='8d9703f5caeb3b621e217989c3a88ee94588277eb4bce447282c21309cbc161f'
v0=Path('scripts/verify_neumann_rectangle_wrap_probe_hot.py').read_text()
v1=Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v2.py').read_text()
expected=v0.replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v1','neumann-rectangle-wrap-probe-hot-v2').replace(
'ec01ca5615a879a9375f5e20ffdf3b5bd532564559b990b5b973810f7228b508','8d9703f5caeb3b621e217989c3a88ee94588277eb4bce447282c21309cbc161f')
assert norm(expected)==norm(v1),'UNEXPECTED_READER_DELTA'
print('WRAP_HOT_V2_EXACT_DELTA=PASS PUBLIC_STATEMENT_UNCHANGED=1 COMPILER_CHECKED=0')
