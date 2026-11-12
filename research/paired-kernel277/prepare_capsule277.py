"""Metadata fabrication only: source bytes/hash/base64, no numpy/scipy/math run."""
from pathlib import Path
import base64,json,hashlib,shutil,difflib
P=Path(__file__).resolve().parent;W=P.parents[1]
old=Path(r'D:\Datos\the-eriksson-programme\autonomia\evidencia-274\production-b')
raw=(P/'diagnostic277B.py').read_bytes();H=hashlib.sha256(raw).hexdigest()
if H!='256362a3d76b4c3609d3bba9f58966ddf05776f27f1789f6a151ada99735ada5':raise ValueError('Parent frozen B source changed')
if hashlib.sha256((P/'diagnostic277.py').read_bytes()).hexdigest()!='ba9f495125acad9f6ddd12d64564f7e966324ebc52eb8677dc4ee75427f3d984':raise ValueError('Original A not preserved')
(P/'launch277.py').write_text((P/'bootstrap277-template.txt').read_text().replace('EMBEDDED_HASH',H).replace('EMBEDDED_BASE64',base64.b64encode(raw).decode()),encoding='utf-8',newline='\n')
(P/'run_owned_after_gate.ps1').write_text((P/'outer277-template.txt').read_text().replace('EMBEDDED_HASH',H),encoding='utf-8',newline='\n')
shutil.copyfile(old/'capture_cli_atomic.ps1',P/'capture_cli_atomic.ps1')
text=(old/'readback_after_stop.ps1').read_text().replace("$out=Join-Path $PSScriptRoot 'attempt-b'","$out='D:\\Datos\\the-eriksson-programme\\autonomia\\evidencia-277\\attempt-a'")
text=text.replace('tep274-build-b-sessions.json','tep277-diagnostic-sessions.json')
(P/'readback_after_stop.ps1').write_text(text,encoding='utf-8',newline='\n')
names=['diagnostic277B.py','launch277.py','capture_cli_atomic.ps1','run_owned_after_gate.ps1','readback_after_stop.ps1']
rows=[{'path':n,'bytes':(P/n).stat().st_size,'sha256':hashlib.sha256((P/n).read_bytes()).hexdigest()} for n in names]
(P/'RUNNER-HASHES.json').write_text(json.dumps(rows,indent=2)+'\n',encoding='utf-8')
(P/'A-to-B-full-delta.diff').write_text(''.join(difflib.unified_diff((P/'diagnostic277.py').read_text().splitlines(True),(P/'diagnostic277B.py').read_text().splitlines(True),fromfile='immutable-A/diagnostic277.py',tofile='preferred-B/diagnostic277B.py')),encoding='utf-8')
print(json.dumps({'diagnostic_B_raw_sha256':H,'runner_manifest_raw_sha256':hashlib.sha256((P/'RUNNER-HASHES.json').read_bytes()).hexdigest(),'operative_files':rows},indent=2))
