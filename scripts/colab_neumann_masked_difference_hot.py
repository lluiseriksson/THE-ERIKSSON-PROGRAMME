#!/usr/bin/env python3
"""Bounded Mathlib-only boundary-mask diagnostic; no physical kernel or inverse seal."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import tarfile
import time

BASE = '98f4337e06271a7d5e3957450440292db0f79168'
ROOT = Path('/content/hrpoly-neumann-character-normalization-promoted-cold-v1')
OUT = Path('/content/neumann-masked-difference-hot-v1')
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
DRAFTS = {
    "tmp/NeumannMaskedDifferenceRepro.lean": "70903fca9cf0e0510bf300f8e77b01d97da5bcd2d1b165adce98cea037814b09"
}
NAMES = {
    "masked_difference_repro": [
        "YangMills.RG.neumannMaskedForwardDifference",
        "YangMills.RG.neumannMaskedBackwardDifference"
    ]
}
COMMANDS = {
    "masked_difference_repro": [
        "lake",
        "env",
        "lean",
        "tmp/NeumannMaskedDifferenceRepro.lean"
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
    if not Path('/content/character-normalization-cold-evidence-preserved.ok').is_file():
        raise RuntimeError('COLD_EVIDENCE_NOT_PRESERVED')
    cold = json.loads(Path(str(ROOT) + '-evidence/evidence.json').read_text())
    if cold['status'] != 'PASS' or cold['source_sha'] != BASE:
        raise RuntimeError('COLD_GATE_NOT_PASS')
    import psutil
    if any(p.info['name'] in ('lean', 'lake')
           for p in psutil.process_iter(['name'])):
        raise RuntimeError('OTHER_COMPILER_ACTIVE')
    gate_path = ROOT / 'scripts/full_green_owner_exact_axiom_gate.py'
    if sha(gate_path.read_bytes()) != GATE_HASH:
        raise RuntimeError('GATE_HASH')
    sys.path.insert(0, str(ROOT / 'scripts'))
    import full_green_owner_exact_axiom_gate as gate
    gate.self_test()
    for path, digest in DRAFTS.items():
        if sha((ROOT / path).read_bytes()) != digest:
            raise RuntimeError('DRAFT_HASH=' + path)
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
            source_blobs=DRAFTS, expected_names=NAMES, records=records, audits=audits)
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
