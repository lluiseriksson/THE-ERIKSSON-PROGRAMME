"""Exact first-failure reader for R2 v1; never returns compiler PASS."""
import argparse
import json
import math
from pathlib import Path
import types
import verify_neumann_coordinate_precision_diagnostic as v

ARCHIVE_HASH = '5ce85f28076e99319b122dabef5949b23ed8858fc59f654091925f3254abfe04'
FAILED = 'carry_physical'

def verify(files):
    for name, digest in [('runner.py', v.RUNNER_HASH), ('durable-base.py', v.BASE_HASH), ('axiom-gate.py', v.GATE_HASH)]:
        v.require(v.sha(files[name]) == digest, 'TRANSPORT=' + name)
    d = json.loads(files['evidence.json'])
    for k, value in dict(status='FAIL', source_sha=v.SOURCE, runner_rev=v.REV,
        mathlib_sha=v.MATHLIB, toolchain_asset_sha256=v.ASSET, source_blobs=v.PINS,
        minimum_ram_gib=40.0, gpu_runtime_authorized=False).items():
        v.require(d.get(k) == value, 'EVIDENCE=' + k)
    c = json.loads(files['coordinate-contract.json'])
    expected = dict(source=v.SOURCE, revision=v.REV, scope=v.SCOPE, cold_seal=False,
        pins=v.PINS, names=v.NAMES, queue=[[s, cmd, v.NAMES.get(s)] for s, cmd in v.COMMANDS.items()],
        base='ddf6fdc1882edddbf063389aab4d455a8ed30801', base_hash=v.BASE_HASH, gate_hash=v.GATE_HASH)
    v.require(set(c) == set(expected) | {'outputs'}, 'CONTRACT_FIELDS')
    for k, value in expected.items(): v.require(c[k] == value, 'CONTRACT=' + k)
    records = d['records']; stages = [r['stage'] for r in records]
    prefix = v.REQUIRED[:v.REQUIRED.index(FAILED) + 1]
    v.require(len(stages) == len(set(stages)), 'DUPLICATES')
    v.require([s for s in stages if s in v.REQUIRED] == prefix, 'PREFIX_ORDER')
    v.require(set(stages) <= set(prefix) | {'apt_update', 'install_zstd'}, 'EXTRA_STAGE')
    v.require(stages[-1] == FAILED, 'STOP_ON_FIRST_ERROR')
    expected_files = {'runner.py','durable-base.py','axiom-gate.py','evidence.json',
        'coordinate-contract.json','gate-contract.json','preflight.json'}
    for r in records:
        s = r['stage']
        v.require(r['exit'] == (1 if s == FAILED else 0) and r['timed_out'] is False, 'EXIT=' + s)
        v.require(math.isfinite(r['seconds']) and r['seconds'] >= 0, 'TIMER=' + s)
        v.require(r['timeout_seconds'] == (120 if s in v.NAMES else 3600), 'TIMEOUT=' + s)
        v.require(r['log_file'] == s+'.log' and v.sha(files[s+'.log']) == r['output_sha256'], 'LOG=' + s)
        v.require(json.loads(files[s+'.json']) == r, 'RECORD=' + s)
        if s in v.COMMANDS: v.require(r['command'] == v.COMMANDS[s] and r['cwd'] == v.ROOT, 'COMMAND=' + s)
        expected_files |= {s+'.log',s+'.json'}
    v.require(files['head.log'].decode().strip() == v.SOURCE, 'HEAD')
    v.require(files['mathlib_pin.log'].decode().strip() == v.MATHLIB, 'MATHLIB')
    for s in ('lean_version','lake_version'): v.require('4.29.0-rc6' in files[s+'.log'].decode(), 'VERSION')
    for path, digest in v.PINS.items():
        n = Path(path).name; v.require(v.sha(files[n]) == digest, 'SOURCE=' + n); expected_files.add(n)
    output_names = {'NeumannCoordinateProductRepro.olean','NeumannHalfCellPhaseRepro.olean',
        'NeumannEntireAverageHalfCellPhaseDraft.olean','NeumannCoordinateAliasReflectionDraft.olean'}
    v.require(set(c['outputs']) == output_names, 'OUTPUT_SET')
    for n, digest in c['outputs'].items(): v.require(bool(files[n]) and v.sha(files[n]) == digest, 'OUTPUT=' + n)
    expected_files |= output_names
    v.require(set(files) == expected_files, 'FILE_SET')
    gate = types.ModuleType('pinned_gate'); exec(compile(files['axiom-gate.py'], 'pinned_gate', 'exec'), gate.__dict__)
    audits = {s: gate.exact_axioms(files[s+'.log'].decode(), names) for s,names in v.NAMES.items() if s in stages and s != FAILED}
    error = files[FAILED+'.log'].decode()
    v.require('tmp/NeumannCoordinateMomentumCarryDraft.lean:79:2: error: unsolved goals' in error and 'if True then -z mu else z mu' in error, 'FIRST_ERROR')
    v.require('sorryAx' in error, 'FAILED_DECLARATIONS_NOT_ACCEPTED')
    return dict(status='VERIFIED_DIAGNOSTIC_FAIL', cold_seal=False, source=v.SOURCE,
        first_error=error, records=records, prefix_audits=audits, outputs=c['outputs'],
        phase_physical='NOT_EXECUTED', scope='preservation of failed R2 diagnostic only')

def main():
    p=argparse.ArgumentParser(); p.add_argument('--archive',type=Path,required=True); p.add_argument('--destination',type=Path,required=True)
    a=p.parse_args(); v.require(a.archive.stat().st_size < 32*2**20, 'SIZE')
    blob=a.archive.read_bytes(); v.require(v.sha(blob)==ARCHIVE_HASH,'ARCHIVE_HASH')
    raw=v.unpack(blob); prefix='hrpoly-'+v.REV+'-evidence/'
    v.require(all(n.startswith(prefix) and '/' not in n[len(prefix):] for n in raw),'PREFIX')
    files={n[len(prefix):]:b for n,b in raw.items()}; report=verify(files)
    report['archive_sha256']=ARCHIVE_HASH
    payload=(json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
    v.require(not a.destination.exists(),'NO_OVERWRITE'); a.destination.mkdir()
    for n,b in files.items(): (a.destination/n).write_bytes(b)
    (a.destination/a.archive.name).write_bytes(blob)
    (a.destination/'independent-verification.json').write_bytes(payload)
    print('STATUS='+report['status']); print('REPORT_SHA256='+v.sha(payload))

if __name__ == '__main__': main()
