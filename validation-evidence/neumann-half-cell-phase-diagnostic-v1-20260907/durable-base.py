#!/usr/bin/env python3
"""Step 13 cold gate: exact hot-verified source, complete durable child logs.

No restored project graph. This is an intermediate focal/audit seal, not a
repo-wide or terminal hRpoly validation. Retain only for evidence download.
"""
from __future__ import annotations

import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import types
import urllib.request

SOURCE = 'eef777d32878297d9e143cbfaff82c290fbb9be1'
URL = ('https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
       + SOURCE + '/scripts/colab_qprime_row_validation.py')
with urllib.request.urlopen(URL, timeout=60) as response:
    blob = response.read()
digest = hashlib.sha256(blob).hexdigest()
print('BASE_RUNNER_SHA256=' + digest, flush=True)
if digest != '2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e':
    raise RuntimeError('BASE_RUNNER_HASH_MISMATCH')
runner = types.ModuleType('full_green_arbitrary_residue_cold_base')
exec(compile(blob, URL, 'exec'), runner.__dict__)

runner.RUNNER_REV = 'cmp99-full-green-arbitrary-residue-cold-v1'
runner.SOURCE_SHA = SOURCE
runner.ROOT = Path('/content/hrpoly-cmp99-full-green-arbitrary-residue-cold-v1')
runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
runner.SOURCE_BLOBS = {
    'YangMills/RG/BalabanCMP99FullGreenArbitraryResidueBound.lean':
        '702ed2e146fd33a5d83ca0843d4c8b58c3efaca3681ad572259fc09a66faccdc',
    'YangMills/RG/BalabanCMP99FullGreenArbitraryResidueBoundAudit.lean':
        '14ca55f49a2c360e527a875bb02e712b5c6a7c2bc588d7e6e42077a76f53a6b2',
}
EXPECTED = frozenset({
    'YangMills.RG.norm_cmp89Eq246PhysicalZeroMassGreen_le_signedLatticeWeight',
    'YangMills.RG.cmp89Eq246DirectedFullSolutionSumBound_nonneg_of_window',
    'YangMills.RG.tsum_norm_cmp89Eq246FullGreen_arbitraryResidue_le_centeredPeriodic',
    'YangMills.RG.norm_tsum_cmp89Eq246FullGreen_arbitraryResidue_le_centeredPeriodic',
})
runner.QUEUE = [
    ('full_green_residue_focal', ['lake', 'build',
        'YangMills.RG.BalabanCMP99FullGreenArbitraryResidueBound'], None),
    ('full_green_residue_audit', ['lake', 'env', 'lean',
        'YangMills/RG/BalabanCMP99FullGreenArbitraryResidueBoundAudit.lean'], EXPECTED),
]


def parse_axioms(output: str, expected: frozenset[str]) -> None:
    compact = re.sub(r'\s+', '', output)
    if any(name in compact for name in ('sorryAx', 'ofReduceBool')):
        raise RuntimeError('FORBIDDEN_AXIOM')
    blocks = re.findall(r"'([^']+)'dependsonaxioms:\[([^\]]*)\]", compact)
    if len(blocks) != len(expected) or {name for name, _ in blocks} != expected:
        raise RuntimeError('AXIOM_DECLARATIONS_MISMATCH')
    for name, body in blocks:
        if {item for item in body.split(',') if item} - runner.ALLOWED_AXIOMS:
            raise RuntimeError('UNEXPECTED_AXIOM=' + name)
    print('AXIOM_GATE=PASS DECLARATIONS=' + str(len(blocks)), flush=True)


def preflight() -> list[dict]:
    records = []
    for code in (0, 7):
        start = time.perf_counter()
        child = subprocess.run([sys.executable, '-c', f'raise SystemExit({code})'],
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        elapsed = time.perf_counter() - start
        if child.returncode != code or not math.isfinite(elapsed) or elapsed < 0:
            raise RuntimeError('PORTABLE_EXIT_TIMER_PREFLIGHT_FAILED')
        records.append({'expected_exit': code, 'actual_exit': child.returncode,
                        'seconds': elapsed})
    sample = "'test' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]"
    parse_axioms(sample, frozenset({'test'}))
    for bad in (sample.replace('Quot.sound', 'sorryAx'),
                sample.replace('Quot.sound', 'ofReduceBool'),
                sample.replace('Quot.sound', 'Unapproved.axiom'),
                sample.replace("'test'", "'wrong'")):
        try:
            parse_axioms(bad, frozenset({'test'}))
        except RuntimeError:
            continue
        raise RuntimeError('AXIOM_REJECTION_PREFLIGHT_FAILED')
    print('PREFLIGHT=PASS ' + json.dumps(records), flush=True)
    return records


def run(stage: str, command: list[str], *, cwd: Path | None = None) -> str:
    if not re.fullmatch(r'[a-z0-9_]+', stage):
        raise RuntimeError('INVALID_STAGE_NAME')
    if any(record['stage'] == stage for record in runner.RECORDS):
        raise RuntimeError('DUPLICATE_STAGE=' + stage)
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    log = runner.EVIDENCE / (stage + '.log')
    print('STAGE=' + stage + ' CMD=' + json.dumps(command), flush=True)
    start = time.perf_counter()
    with log.open('wb') as stream:
        child = subprocess.run(command, cwd=cwd, env=os.environ.copy(),
                               stdout=stream, stderr=subprocess.STDOUT)
    elapsed = time.perf_counter() - start
    data = log.read_bytes()
    record = {'stage': stage, 'exit': child.returncode, 'seconds': elapsed,
              'output_sha256': hashlib.sha256(data).hexdigest(),
              'log_file': log.name, 'command': command,
              'cwd': str(cwd) if cwd else None}
    runner.RECORDS.append(record)
    temp = runner.EVIDENCE / (stage + '.json.tmp')
    temp.write_text(json.dumps(record, sort_keys=True) + '\n', encoding='utf-8')
    temp.replace(runner.EVIDENCE / (stage + '.json'))
    output = data.decode('utf-8', errors='replace')
    print(output[-6000:], flush=True)
    print(f'STAGE={stage} EXIT={child.returncode} SECONDS={elapsed:.3f}', flush=True)
    if child.returncode != 0:
        raise RuntimeError('FIRST_ERROR=' + stage)
    return output


runner.run = run
runner.parse_axioms = parse_axioms
original_make_evidence = runner.make_evidence


def make_evidence(status: str, opened: str) -> tuple[str, str]:
    runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
    for record in runner.RECORDS:
        if runner.sha256(runner.EVIDENCE / record['log_file']) != record['output_sha256']:
            raise RuntimeError('DURABLE_LOG_HASH_MISMATCH=' + record['stage'])
    (runner.EVIDENCE / 'preflight.json').write_text(
        json.dumps(PREFLIGHT, sort_keys=True) + '\n', encoding='utf-8')
    (runner.EVIDENCE / 'gate-contract.json').write_text(json.dumps({
        'base_runner_sha256': digest, 'source_sha': SOURCE,
        'expected_axiom_names': sorted(EXPECTED),
        'project_build_cache_restored': False,
        'scope': 'intermediate focal/audit; not root or terminal hRpoly',
    }, sort_keys=True) + '\n', encoding='utf-8')
    return original_make_evidence(status, opened)


runner.make_evidence = make_evidence
PREFLIGHT: list[dict] = []
if __name__ == '__main__':
    if runner.ROOT.exists() or runner.EVIDENCE.exists() or runner.ARCHIVE.exists():
        raise RuntimeError('FRESH_RUN_REQUIRED_NO_REEXECUTION')
    PREFLIGHT = preflight()
    from google.colab import runtime
    saved_unassign = runtime.unassign
    runtime.unassign = lambda: print('RUNTIME_RETAINED_FOR_EVIDENCE_DOWNLOAD=1', flush=True)
    try:
        raise SystemExit(runner.main())
    finally:
        runtime.unassign = saved_unassign
