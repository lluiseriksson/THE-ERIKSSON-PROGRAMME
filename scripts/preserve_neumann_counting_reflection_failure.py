"""Preserve the exact v1 FAIL. No compiler/network/pool; no mathematical PASS."""
import argparse
import json
import math
from pathlib import Path
import types
import verify_neumann_counting_reflection_diagnostic as v

OUTER = '97b8b08e71002036bdbe45b6f6e23547468e296a2bf566a61180514bc056f30a'
INNER = 'cae59efad28b957bd27df86316b06d3a6ae4b46ee5815cfe9c3c66ba841dd0de'
LOG = 'd62460143bb847114d7541ffcee9d06f53b942bf4a02746b467ae7abd3a89457'


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--destination', type=Path, required=True)
    p.add_argument('--axiom-helper', type=Path, required=True)
    a = p.parse_args()
    v.require(not a.destination.exists(), 'NO_OVERWRITE')
    v.require(a.archive.stat().st_size < 8_000_000, 'SIZE')
    blob = a.archive.read_bytes()
    v.require(v.sha(blob) == OUTER, 'OUTER_HASH')
    outer = v.unpack(blob)
    pre = v.REV + '-launch/'
    inner_name = 'hrpoly-' + v.REV + '-evidence.tar.gz'
    v.require(set(outer) == {pre+'runner.py', pre+'diagnostic.log',
        pre+'launch-final-status.json', inner_name}, 'OUTER_FILES')
    v.require(v.sha(outer[pre+'runner.py']) == v.RUNNER_HASH, 'RUNNER')
    launch = json.loads(outer[pre+'launch-final-status.json'])
    v.require(launch['status'] == 'FAIL' and launch['exit'] == 1 and
        launch['cold_seal'] is False and launch['source'] == v.SOURCE, 'LAUNCH')
    v.require(v.sha(outer[pre+'diagnostic.log']) == launch['log_sha256'], 'LAUNCH_LOG')
    v.require(v.sha(outer[inner_name]) == INNER == launch['inner_sha256'], 'INNER_HASH')
    nested = v.unpack(outer[inner_name])
    ip = 'hrpoly-' + v.REV + '-evidence/'
    v.require(all(n.startswith(ip) for n in nested), 'INNER_PREFIX')
    files = {n[len(ip):]: b for n,b in nested.items()}
    data = json.loads(files['evidence.json'])
    v.require(data['status'] == 'FAIL' and data['source_sha'] == v.SOURCE and
        data['source_blobs'] == v.BLOBS and data['mathlib_sha'] == v.MATHLIB and
        data['toolchain_asset_sha256'] == v.ASSET, 'EVIDENCE')
    records = data['records']
    stages = [r['stage'] for r in records]
    v.require(len(stages) == len(set(stages)) and
        [s for s in stages if s in v.REQUIRED] == v.REQUIRED and
        set(stages) <= set(v.REQUIRED)|{'apt_update','install_zstd'}, 'STAGES')
    v.require(all(r['exit'] == 0 for r in records[:-1]) and
        records[-1]['stage'] == 'counting_reflection_draft' and
        records[-1]['exit'] == 1, 'FIRST_NONZERO')
    for r in records:
        s = r['stage']
        v.require(math.isfinite(r['seconds']) and r['seconds'] >= 0, 'TIMER')
        v.require(json.loads(files[s+'.json']) == r and
            v.sha(files[s+'.log']) == r['output_sha256'], 'RECORD_LOG='+s)
        if s in v.COMMANDS:
            v.require(r['command'] == v.COMMANDS[s] and r['cwd'] == v.ROOT, 'COMMAND='+s)
    for name,digest in v.BLOBS.items():
        v.require(v.sha(files[Path(name).name]) == digest, 'SOURCE_BLOB')
    fail = files['counting_reflection_draft.log']
    v.require(v.sha(fail) == LOG and b':34:46: error:' in fail, 'EXACT_FIRST_ERROR')
    helper = a.axiom_helper.read_bytes()
    v.require(v.sha(helper) == v.GATE_HASH, 'AXIOM_HELPER')
    gate = types.ModuleType('pinned_gate')
    exec(compile(helper,str(a.axiom_helper),'exec'), gate.__dict__)
    repro = gate.exact_axioms(files['counting_reflection_repro.log'].decode(),
        v.NAMES['counting_reflection_repro'])
    rejected = False
    try:
        gate.exact_axioms(fail.decode(), v.NAMES['counting_reflection_draft'])
    except ValueError:
        rejected = True
    v.require(rejected, 'FAILED_MODULE_MUST_BE_REJECTED')
    root = a.destination
    root.mkdir(parents=True, exist_ok=False)
    (root/a.archive.name).write_bytes(blob)
    for name,payload in {**outer, **nested}.items():
        target = root/Path(name)
        target.parent.mkdir(parents=True,exist_ok=True)
        with target.open('xb') as out:
            out.write(payload)
    report = dict(preservation_verification='PASS', artifact_status='FAIL',
        cold_seal=False, source=v.SOURCE, outer_sha256=OUTER, inner_sha256=INNER,
        first_error_log_sha256=LOG, first_error='draft:34:46 rewrite failed',
        stages=len(records), records=records, repro_axioms=repro,
        failed_module_axioms_rejected=True, mathematical_seal=False)
    payload = (json.dumps(report,sort_keys=True,indent=2)+'\n').encode()
    (root/'independent-failure-verification.json').write_bytes(payload)
    print('FAILURE_EVIDENCE_PRESERVED ARTIFACT_STATUS=FAIL COLD_SEAL=0')
    print('REPORT_SHA256='+v.sha(payload))
    print('FIRST_ERROR_LOG_SHA256='+LOG)


if __name__ == '__main__':
    main()
