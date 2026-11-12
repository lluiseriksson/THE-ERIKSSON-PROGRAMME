"""Source-byte editing/hash/base64 preparation ONLY. Never imports diagnostic."""
from pathlib import Path
import base64,json,hashlib,shutil
P=Path(__file__).resolve().parent;OLD=P.parent/'paired-kernel277'
raw=(P/'diagnostic281B.py').read_bytes();H=hashlib.sha256(raw).hexdigest()
def write(name,text):
    with (P/name).open('x',encoding='utf-8',newline='\n') as f:f.write(text)
write('launch281.py',(P/'bootstrap281-template.txt').read_text(encoding='utf-8').replace('EMBEDDED_HASH',H).replace('EMBEDDED_BASE64',base64.b64encode(raw).decode()))
outer=(OLD/'outer277-template.txt').read_text(encoding='utf-8').replace('277','281').replace('801004ccd85170de6b39146decd34cc6400c2060','4ba7c61adb94d80f4cb985ab78e84d8346171b02').replace('research/paired-kernel281','research/full-cost281').replace('EMBEDDED_HASH',H)
# Parent full returned audit still checks every actual inner command; source
# gate additionally binds all three standalone receipt command records here.
outer=outer.replace("$receipt.status -cne $summary.status)","$receipt.status -cne $summary.status -or @($receipt.commands).Count -ne 3 -or @($receipt.commands|Where-Object{$_.exit -ne 0 -or $_.timed_out -ne $false}).Count -ne 0)")
write('run_owned_after_gate.ps1',outer)
shutil.copyfile(OLD/'capture_cli_atomic.ps1',P/'capture_cli_atomic.ps1')
write('readback_after_stop.ps1',(OLD/'readback_after_stop.ps1').read_text(encoding='utf-8').replace('277','281'))
write('.gitattributes','* -text\n')
names=['diagnostic281B.py','launch281.py','capture_cli_atomic.ps1','run_owned_after_gate.ps1','readback_after_stop.ps1']
rows=[{'path':name,'bytes':(P/name).stat().st_size,'sha256':hashlib.sha256((P/name).read_bytes()).hexdigest()} for name in names]
write('RUNNER-HASHES.json',json.dumps(rows,indent=2)+'\n')
print(json.dumps({'source_raw_sha256':H,'runner_manifest_sha256':hashlib.sha256((P/'RUNNER-HASHES.json').read_bytes()).hexdigest(),'operative_files':rows},indent=2))
