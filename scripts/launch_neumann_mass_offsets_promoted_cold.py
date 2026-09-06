"""One-shot launcher for the six-name mass/complete-offset intermediate cold gate.

No CI, credentials, Drive or interactive uploads. Preserve all failures.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tarfile
import time
import traceback
import urllib.request

REV = 'neumann-mass-offsets-promoted-cold-v1'
SOURCE = '9bb957757b6454871eaea6e26aed8c95dc576b3c'
WORK = Path('/content/neumann-mass-offsets-promoted-cold-v1-launch')
INNER = Path('/content/hrpoly-' + REV + '-evidence.tar.gz')
OUTER = Path('/content/neumann-mass-offsets-promoted-cold-v1-preservation-20260906.tar.gz')
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
FILES = {
    'colab_neumann_mass_offsets_promoted_cold.py': (
        '48d3b3df4f214a6335f1b7c438fcb945731661fb',
        '5c46e6caf65796bfba486cebc498c42c8d701978df398bc4798a58b33168f625'),
    'verify_neumann_mass_offsets_promoted_cold.py': (
        '48d3b3df4f214a6335f1b7c438fcb945731661fb',
        'bb097d627a5405373c2ebf93d43c6706bf1bad8f585af8ce781b11aeef4343c1'),
    'verify_cmp99_full_green_residue_cold.py': (SOURCE,
        '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c'),
    'full_green_owner_exact_axiom_gate.py': (SOURCE,
        '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'),
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    if WORK.exists() or OUTER.exists() or INNER.exists():
        raise RuntimeError('ALREADY_STARTED_NO_REEXECUTION')
    WORK.mkdir()
    records = []
    status = 'FAIL'

    def child(stage, command):
        log = WORK / (stage + '.log')
        start = time.perf_counter()
        with log.open('xb') as stream:
            p = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
        r = dict(stage=stage,command=command,exit=p.returncode,
            seconds=time.perf_counter()-start,log_sha256=sha(log))
        records.append(r)
        temp = WORK / 'launch-records.json.tmp'
        temp.write_text(json.dumps(records,sort_keys=True)+'\n')
        temp.replace(WORK / 'launch-records.json')
        print(json.dumps(r,sort_keys=True),flush=True)
        if p.returncode:
            print(log.read_text(errors='replace')[-8000:],flush=True)
            raise RuntimeError('FIRST_ERROR='+stage)

    try:
        print('RUNNER_REV='+REV+' SOURCE_SHA='+SOURCE,flush=True)
        for name,(commit,digest) in FILES.items():
            with urllib.request.urlopen(RAW+commit+'/scripts/'+name,timeout=60) as response:
                blob=response.read()
            if hashlib.sha256(blob).hexdigest()!=digest:
                raise RuntimeError('TRANSPORT_HASH='+name)
            (WORK/name).write_bytes(blob)
            print('TRANSPORT_OK='+name+' SHA256='+digest,flush=True)
        (WORK/'transport.json').write_text(json.dumps(FILES,sort_keys=True)+'\n')
        verifier=str(WORK/'verify_neumann_mass_offsets_promoted_cold.py')
        child('verifier_self_test',[sys.executable,verifier,'--helpers',str(WORK),'--self-test'])
        child('physical_cold_graph',[sys.executable,str(WORK/'colab_neumann_mass_offsets_promoted_cold.py')])
        child('archive_verifier',[sys.executable,verifier,'--helpers',str(WORK),
            '--archive',str(INNER),'--sha256',sha(INNER)])
        status='PASS'
    except Exception:
        traceback.print_exc()
    finally:
        (WORK/'launch-final-status.json').write_text(json.dumps(dict(
            status=status,source=SOURCE,revision=REV,cold_seal=True),sort_keys=True)+'\n')
        with tarfile.open(OUTER,'w:gz') as tar:
            tar.add(WORK,arcname=WORK.name)
            if INNER.is_file(): tar.add(INNER,arcname=INNER.name)
            tar.add(Path(__file__),arcname='launch_neumann_mass_offsets_promoted_cold.py')
        print('LAUNCH_FINAL_STATUS='+status+' INTERMEDIATE_COLD_GRAPH=1',flush=True)
        print('PRESERVATION_ARCHIVE='+str(OUTER),flush=True)
        print('PRESERVATION_SHA256='+sha(OUTER),flush=True)
        print('RUNTIME_RETAINED_FOR_EVIDENCE=1',flush=True)
    return 0 if status=='PASS' else 1


if __name__=='__main__': raise SystemExit(main())
