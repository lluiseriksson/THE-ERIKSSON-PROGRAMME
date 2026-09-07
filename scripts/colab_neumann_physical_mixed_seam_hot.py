#!/usr/bin/env python3
"""Bounded physical mixed seam HOT, after reindex cold evidence preservation; never a cold seal."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import tarfile
import time
import urllib.request

ROOT = Path('/content/hrpoly-neumann-mixed-image-reindex-promoted-cold-v1')
BASE = 'fa898ff5d8bf724fa4b6e629da7260383ef54ecc'
SOURCE = 'e4f037a52050fd9c539f5b30476d7a59d9f59688'
DRAFT = 'tmp/NeumannPhysicalMixedSeamDraft.lean'
DIGEST = '75a86db01f24def9dd7d5c2b888f8ed4ef8e68751f77a53b3330b59de55c2fd0'
GATE_DIGEST = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
OUT = Path('/content/neumann-physical-mixed-seam-hot-v1')
NAMES = set([
    "YangMills.RG.summable_neumannPhysicalMixedGreenSeries",
    "YangMills.RG.neumannPhysicalMixedGreenSeries_periodic",
    "YangMills.RG.neumannPhysicalMixedGreenSeries_properBoundary"
])


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    if OUT.exists():
        raise RuntimeError('NO_REEXECUTION')
    if subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT,
                               text=True).strip() != BASE:
        raise RuntimeError('WRONG_BASE_SOURCE')
    # Explicit operator acknowledgement only after the preceding archive has
    # been downloaded and independently checked. Not a mathematical premise.
    if not Path('/content/mixed-reindex-cold-evidence-preserved.ok').is_file():
        raise RuntimeError('PREVIOUS_EVIDENCE_NOT_PRESERVED')
    import psutil
    if any(p.info['name'] in ('lean', 'lake')
           for p in psutil.process_iter(['name'])):
        raise RuntimeError('OTHER_COMPILER_ACTIVE')
    gate_path = ROOT / 'scripts/full_green_owner_exact_axiom_gate.py'
    if sha(gate_path.read_bytes()) != GATE_DIGEST:
        raise RuntimeError('GATE_HASH')
    sys.path.insert(0, str(ROOT / 'scripts'))
    import full_green_owner_exact_axiom_gate as gate
    gate.self_test()
    bins = list(Path('/content/lean-4.29.0-rc6-linux').rglob('bin/lake'))
    if len(bins) != 1:
        raise RuntimeError('AMBIGUOUS_TOOLCHAIN')
    os.environ['PATH'] = str(bins[0].parent) + ':' + os.environ['PATH']
    OUT.mkdir()
    (OUT / 'runner.py').write_bytes(Path(__file__).read_bytes())
    records = []
    audits = {}
    status = 'FAIL'
    try:
        url = ('https://raw.githubusercontent.com/lluiseriksson/'
               'THE-ERIKSSON-PROGRAMME/' + SOURCE + '/' + DRAFT)
        data = urllib.request.urlopen(url, timeout=60).read()
        if sha(data) != DIGEST:
            raise RuntimeError('DRAFT_HASH')
        if (ROOT / DRAFT).exists():
            raise RuntimeError('UNEXPECTED_EXISTING_DRAFT')
        (ROOT / DRAFT).write_bytes(data)
        (OUT / 'source.lean').write_bytes(data)
        commands = [
            ('prerequisites', ['lake', 'build',
                'YangMills.RG.NeumannMixedImageReindex',
                'YangMills.RG.NeumannPhysicalFullFlag',
                'YangMills.RG.NeumannPhysicalMixedSummability',
                'YangMills.RG.NeumannPhysicalBoundaryTransfer']),
            ('physical_seam', ['lake', 'env', 'lean', DRAFT])]
        for stage, command in commands:
            print('STAGE=' + stage, flush=True)
            start = time.monotonic()
            child = subprocess.run(command, cwd=ROOT, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log = child.stdout.encode()
            (OUT / (stage + '.log')).write_bytes(log)
            record = dict(stage=stage, command=command, cwd=str(ROOT),
                exit=child.returncode, seconds=time.monotonic() - start,
                log_sha256=sha(log))
            records.append(record)
            print(json.dumps(record), flush=True)
            print(child.stdout, flush=True)
            if child.returncode:
                raise RuntimeError('FIRST_ERROR=' + stage)
            if stage == 'physical_seam':
                audits = gate.exact_axioms(child.stdout, NAMES)
        status = 'PASS'
    except Exception as error:
        print(repr(error), flush=True)
    finally:
        report = dict(status=status, cold_seal=False, base_source=BASE,
            overlay_source=SOURCE, overlay_path=DRAFT, overlay_sha256=DIGEST,
            records=records, audits=audits, expected_names=sorted(NAMES))
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

