"""Exact v2-to-v3 instrumental delta, parent evidence and public statement. No Lean."""
import ast,hashlib,runpy,subprocess
from pathlib import Path
runpy.run_path('scripts/test_neumann_rectangle_wrap_probe_hot_actual.py',run_name='__main__')
def blob(ref,path):
    return subprocess.check_output(['git','cat-file','blob',ref+':'+path],timeout=5)
def norm(s):
    return ast.dump(ast.parse(s))
old='70072b776d85c42e5f5935160c885b2b24fe3431'
new='0a8cef1f347f37a397aedbc4ecdae3ebb983c4b9'
src='tmp/NeumannRectangleWrapProbeDraft.lean'
before=blob(old,src).decode()
after=blob(new,src).decode()
def statement(s):
    return s.split('theorem neumannRectangle_siteFit_retains_wrapBond :',1)[1].split(' := by',1)[0]
assert statement(before)==statement(after),'PUBLIC_WITNESS_CHANGED'
assert 'maxRecDepth' not in after and 'maxHeartbeats' not in after
assert hashlib.sha256(after.encode()).hexdigest()=='bdc33d7b56f1215d43cc13596f0a23c28a32d952a51c4ab685bfe1a5dc7eef5c'
r0=Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v2.py').read_text()
r1=Path('scripts/colab_neumann_rectangle_wrap_probe_hot_v3.py').read_text()
expected=r0.replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v2','neumann-rectangle-wrap-probe-hot-v3').replace(
'c7e713335bef48fdca25cc332e3fa241d3fb509e5eca5038daa1c64cafbc9ee8','bdc33d7b56f1215d43cc13596f0a23c28a32d952a51c4ab685bfe1a5dc7eef5c')
assert norm(expected)==norm(r1),'UNEXPECTED_RUNNER_DELTA'
rb=blob('b624f0a53822f4ea6e234587ced5f1c0f16a6ed2','scripts/colab_neumann_rectangle_wrap_probe_hot_v3.py')
assert hashlib.sha256(rb).hexdigest()=='16bbb9de0ee2c3676ab421967419d238524c40fb8c30b84db865e51a5700c531'
v0=Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v2.py').read_text()
v1=Path('scripts/verify_neumann_rectangle_wrap_probe_hot_v3.py').read_text()
expected=v0.replace(old,new).replace('neumann-rectangle-wrap-probe-hot-v2','neumann-rectangle-wrap-probe-hot-v3').replace(
'8d9703f5caeb3b621e217989c3a88ee94588277eb4bce447282c21309cbc161f','16bbb9de0ee2c3676ab421967419d238524c40fb8c30b84db865e51a5700c531')
assert norm(expected)==norm(v1),'UNEXPECTED_READER_DELTA'
print('WRAP_HOT_V3_EXACT_DELTA=PASS PUBLIC_STATEMENT_UNCHANGED=1 COMPILER_CHECKED=0')
