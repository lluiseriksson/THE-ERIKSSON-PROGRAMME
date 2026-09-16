#!/usr/bin/env python3
"""Bounded literal alias integral composition; not the physical inverse equation."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import tarfile
import time
import urllib.request

OVERLAY_SOURCE = 'f308441f2cf19b2294189cab14d1a1d6d1217330'

BASE = 'ba2998c4f22707ed0f828c741ae6aa1efb924a36'
ROOT = Path('/content/hrpoly-neumann-alias-physical-integral-promoted-cold-v1')
OUT = Path('/content/neumann-physical-readout-integral-hot-v1')
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
DRAFTS = {
    "tmp/NeumannPhysicalReadoutIntegralDraft.lean": "cd0a8e40a5003eb4665326b53c355a62d661a62539baff4507e3398187590fd7"
}
NAMES = {
    "readout_integral": [
        "YangMills.RG.neumannPhysicalEndpoint_aliasPhase",
        "YangMills.RG.neumannPhysicalEndpoint_aliasPrecision_readout",
        "YangMills.RG.neumannPhysicalBrillouinParameter_ae_bound",
        "YangMills.RG.neumannPhysicalBrillouin_fullSolutionDomain_ae",
        "YangMills.RG.neumannPhysicalAliasPrecisionReadout_integral"
    ]
}
COMMANDS = {
    "mass_uniform_prerequisite": [
        "lake",
        "build",
        "YangMills.RG.BalabanCMP89Eq246MassUniformAnalyticDomain"
    ],
    "readout_integral": [
        "lake",
        "env",
        "lean",
        "tmp/NeumannPhysicalReadoutIntegralDraft.lean"
    ]
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    if OUT.exists():
        raise RuntimeError('NO_REEXECUTION')
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT,
                               text=True).strip() != BASE:
        raise RuntimeError('WRONG_SOURCE')
    if not Path('/content/alias-integral-cold-evidence-preserved.json').is_file():
        raise RuntimeError('COLD_EVIDENCE_NOT_PRESERVED')
    cold = json.loads(Path(str(ROOT) + '-evidence/evidence.json').read_text())
    if cold['status'] != 'PASS' or cold['source_sha'] != BASE:
        raise RuntimeError('COLD_GATE_NOT_PASS')
    ack = json.loads(Path('/content/alias-integral-cold-evidence-preserved.json').read_text())
    if ack.get('source_sha') != BASE or ack.get('status') != 'PASS':
        raise RuntimeError('COLD_PRESERVATION_ACK')
    if sha(Path(str(ROOT) + '-evidence.tar.gz').read_bytes()) != ack.get('archive_sha256'):
        raise RuntimeError('COLD_ARCHIVE_HASH')
    parent = Path('/content/neumann-physical-endpoint-readout-hot-v1.tar.gz')
    if sha(parent.read_bytes()) != '08c8518f5ef1037268e92038dc0cfef6b37baab0c827a169e44b4f7bc426116c':
        raise RuntimeError('PARENT_HOT_HASH')
    if not Path('/content/endpoint-readout-hot-preserved.ok').is_file():
        raise RuntimeError('PARENT_HOT_NOT_PRESERVED')
    import psutil
    if any(p.info['name'] in ('lean', 'lake') and p.status() != psutil.STATUS_ZOMBIE
           for p in psutil.process_iter(['name'])):
        raise RuntimeError('OTHER_COMPILER_ACTIVE')
    gate_path = ROOT / 'scripts/full_green_owner_exact_axiom_gate.py'
    if sha(gate_path.read_bytes()) != GATE_HASH:
        raise RuntimeError('GATE_HASH')
    sys.path.insert(0, str(ROOT / 'scripts'))
    import full_green_owner_exact_axiom_gate as gate
    gate.self_test()
    for path, digest in DRAFTS.items():
        url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/' + OVERLAY_SOURCE + '/' + path
        with urllib.request.urlopen(url, timeout=60) as response:
            blob = response.read()
        if sha(blob) != digest:
            raise RuntimeError('OVERLAY_HASH=' + path)
        target = ROOT / path
        if target.exists() and target.read_bytes() != blob:
            raise RuntimeError('EXISTING_DIFFERENT_DRAFT=' + path)
        target.write_bytes(blob)
    bins = list(Path('/content/lean-4.29.0-rc6-linux').rglob('bin/lake'))
    if len(bins) != 1:
        raise RuntimeError('AMBIGUOUS_TOOLCHAIN')
    os.environ['PATH'] = str(bins[0].parent) + ':' + os.environ['PATH']
    OUT.mkdir()
    (OUT / 'runner.py').write_bytes(Path(__file__).read_bytes())
    for path in DRAFTS:
        (OUT / Path(path).name).write_bytes((ROOT / path).read_bytes())
    records, audits = [], {}
    status = 'FAIL'
    try:
        for stage, command in COMMANDS.items():
            print('STAGE=' + stage, flush=True)
            started = time.monotonic()
            child = subprocess.run(command, cwd=ROOT, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            data = child.stdout.encode()
            (OUT / (stage + '.log')).write_bytes(data)
            record = dict(stage=stage, command=command, cwd=str(ROOT),
                exit=child.returncode, seconds=time.monotonic() - started,
                log_sha256=sha(data))
            records.append(record)
            print(json.dumps(record), flush=True)
            print(child.stdout, flush=True)
            if child.returncode:
                raise RuntimeError('FIRST_ERROR=' + stage)
            if stage in NAMES:
                audits[stage] = gate.exact_axioms(child.stdout, set(NAMES[stage]))
        status = 'PASS'
    except Exception as error:
        print(repr(error), flush=True)
    finally:
        report = dict(status=status, cold_seal=False, source_sha=BASE,
            source_blobs=DRAFTS, overlay_source_sha=OVERLAY_SOURCE, expected_names=NAMES, records=records, audits=audits)
        (OUT / 'result.json').write_text(json.dumps(report, sort_keys=True))
        manifest = {p.name: sha(p.read_bytes()) for p in OUT.iterdir() if p.is_file()}
        (OUT / 'manifest.json').write_text(json.dumps(manifest, sort_keys=True))
        archive = Path(str(OUT) + '.tar.gz')
        with tarfile.open(archive, 'w:gz') as tar:
            tar.add(OUT, arcname=OUT.name)
        print('ARCHIVE=' + str(archive), flush=True)
        print('ARCHIVE_SHA256=' + sha(archive.read_bytes()), flush=True)
        print('FINAL_STATUS=' + status, flush=True)
    return 0 if status == 'PASS' else 1

if __name__ == '__main__':
    raise SystemExit(main())
