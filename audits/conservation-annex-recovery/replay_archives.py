"""Recreate the complete certificate from nine immutable source archives."""
from pathlib import Path
from urllib.request import Request, urlopen
import hashlib
import json
import subprocess
import sys

def main():
    sources=json.loads(Path('sources.json').read_text())
    for name,pin in sources.items():
        path=Path(name)
        if path.exists():
            raw=path.read_bytes()
        else:
            with urlopen(Request(pin['url'],headers={'User-Agent':'Eriksson-checklist-audit/1'}),timeout=40) as response:
                raw=response.read()
        if hashlib.sha256(raw).hexdigest()!=pin['sha256']:
            raise ValueError('Source archive differs: '+name)
        if not path.exists():
            path.write_bytes(raw)
    subprocess.run([sys.executable,'annex_recovery.py'],check=True)
    result=json.loads(Path('reconstruction.json').read_text())
    report=json.loads(Path('summary.json').read_text())
    if result['by_dataset']!=report['by_dataset'] or hashlib.sha256(Path('reconstruction.json').read_bytes()).hexdigest()!=report['reconstruction_sha256']:
        raise ValueError('Reconstructed relations differ from archived calculation')
    print(report['reconstruction_sha256'])
if __name__=='__main__':main()
