"""Independent bounded evidence verification; no Lean/network/Git/subprocess."""
import argparse
import json
import math
from pathlib import Path
import types
import neumann_integer_image_contract as C
from verify_neumann_counting_reflection_diagnostic_v2 import unpack

REQUIRED = ['download_toolchain', 'extract_toolchain', 'lean_version', 'lake_version',
            'clone', 'checkout', 'head', 'overlay_text_guard', 'import_prefix_guard',
            'lake_update', 'mathlib_pin', 'cache_get', *C.COMMANDS]
MATHLIB = '07642720480157414db592fa85b626dafb71355b'
ASSET = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def check(files, runner_hash, contract_hash):
    require(C.sha(files['runner.py']) == runner_hash, 'RUNNER_HASH')
    require(C.sha(files['contract.py']) == contract_hash, 'CONTRACT_HASH')
    gate_blob = files['full_green_owner_exact_axiom_gate.py']
    require(C.sha(gate_blob) == C.GATE_HASH, 'GATE_HASH')
    gate = types.ModuleType('pinned_gate')
    exec(compile(gate_blob, 'pinned_gate', 'exec'), gate.__dict__)
    data = json.loads(files['evidence.json'])
    expected = dict(status='PASS', source_sha=C.SOURCE, runner_rev=C.REV,
                    source_blobs=C.BLOBS, minimum_ram_gib=40.0,
                    gpu_runtime_authorized=False, mathlib_sha=MATHLIB,
                    toolchain_asset_sha256=ASSET)
    for key, value in expected.items():
        require(data.get(key) == value, 'FIELD=' + key)
    generic = json.loads(files['gate-contract.json'])
    require(generic.get('source_sha') == C.SOURCE and
            generic.get('base_runner_sha256') == C.BASE_RUNNER_HASH and
            generic.get('project_build_cache_restored') is False and
            generic.get('expected_axiom_names') == sorted(C.NAMES), 'BASE_CONTRACT')
    contract = json.loads(files['image-contract.json'])
    for key, value in dict(source=C.SOURCE, cold_seal=False,
            restored_project_outputs=False, names=sorted(C.NAMES),
            queue=list(C.COMMANDS), leaf_timeout_seconds=120).items():
        require(contract.get(key) == value, 'IMAGE_CONTRACT=' + key)
    inputs = {p: files[Path(p).name] for p in C.BLOBS}
    require(contract['inputs'] == {p: dict(file=Path(p).name, sha256=h)
                                   for p, h in C.BLOBS.items()}, 'INPUT_MAP')
    require(files['mathlib-repro.lean'] == C.minimal_text(inputs), 'EXACT_REPRO_EXTRACTION')
    outputs = contract['outputs']
    require(set(outputs) == {'mathlib-repro.olean', 'image-draft.olean'}, 'OUTPUT_SET')
    for name, digest in outputs.items():
        require(len(files[name]) > 0 and C.sha(files[name]) == digest, 'OUTPUT_HASH=' + name)
    preflight = json.loads(files['preflight.json'])
    require(len(preflight) == 2, 'PREFLIGHT_COUNT')
    for r, code in zip(preflight, (0, 7)):
        require(r['actual_exit'] == r['expected_exit'] == code and
                math.isfinite(r['seconds']) and r['seconds'] >= 0, 'PREFLIGHT')
    records = data['records']
    stages = [r['stage'] for r in records]
    require(len(stages) == len(set(stages)) and
            [s for s in stages if s in REQUIRED] == REQUIRED and
            set(stages) <= set(REQUIRED) | {'apt_update', 'install_zstd'}, 'STAGES')
    expected_files = {'runner.py', 'contract.py', 'full_green_owner_exact_axiom_gate.py',
                      'evidence.json', 'gate-contract.json', 'image-contract.json',
                      'preflight.json', 'mathlib-repro.lean', *outputs,
                      *(Path(p).name for p in C.BLOBS)}
    indexed = {}
    for r in records:
        s = r['stage']
        indexed[s] = r
        require(r['exit'] == 0 and math.isfinite(r['seconds']) and r['seconds'] >= 0,
                'EXIT_OR_TIMER=' + s)
        require(r['log_file'] == s + '.log' and
                C.sha(files[s + '.log']) == r['output_sha256'], 'LOG=' + s)
        require(json.loads(files[s + '.json']) == r, 'RECORD=' + s)
        expected_files |= {s + '.json', s + '.log'}
    require(set(files) == expected_files, 'FILES')
    for s, cmd in C.COMMANDS.items():
        require(indexed[s]['command'] == cmd and indexed[s]['cwd'] == C.ROOT, 'COMMAND=' + s)
    for s in ('image_mathlib_repro', 'image_draft'):
        require(indexed[s]['timed_out'] is False, 'TIMEOUT=' + s)
    require(indexed['checkout']['command'] == ['git', 'checkout', '--detach', C.SOURCE], 'CHECKOUT')
    require(files['head.log'].decode().strip() == C.SOURCE, 'HEAD')
    require(files['mathlib_pin.log'].decode().strip() == MATHLIB, 'MATHLIB')
    require(files['final_clean_source.log'] == b'', 'SOURCE_CHANGED')
    for s in ('lean_version', 'lake_version'):
        require('4.29.0-rc6' in files[s + '.log'].decode(), 'VERSION')
    axioms = {s: gate.exact_axioms(files[s + '.log'].decode(), C.NAMES)
              for s in ('image_mathlib_repro', 'image_draft')}
    return dict(status='PASS', cold_seal=False, source=C.SOURCE,
                stages_verified=len(records), outputs=outputs, axioms=axioms,
                repro_sha256=C.sha(files['mathlib-repro.lean']),
                evidence_sha256=C.sha(files['evidence.json']),
                queue=[indexed[s] for s in C.COMMANDS])


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--sha256', required=True)
    p.add_argument('--runner-sha256', required=True)
    p.add_argument('--contract-sha256', required=True)
    p.add_argument('--destination', type=Path)
    a = p.parse_args()
    require(a.archive.stat().st_size <= 64 * 2**20, 'ARCHIVE_SIZE')
    blob = a.archive.read_bytes()
    require(C.sha(blob) == a.sha256.lower(), 'ARCHIVE_HASH')
    nested = unpack(blob)
    prefix = Path(C.EVIDENCE).name + '/'
    require(all(n.startswith(prefix) and '/' not in n[len(prefix):] for n in nested), 'PREFIX')
    report = check({n[len(prefix):]: b for n, b in nested.items()},
                   a.runner_sha256.lower(), a.contract_sha256.lower())
    report['archive_sha256'] = C.sha(blob)
    payload = (json.dumps(report, sort_keys=True, indent=2) + '\n').encode()
    if a.destination:
        require(not a.destination.exists(), 'NO_OVERWRITE')
        a.destination.mkdir(parents=True)
        (a.destination / a.archive.name).write_bytes(blob)
        for name, content in nested.items():
            target = a.destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open('xb') as out:
                out.write(content)
        (a.destination / 'independent-verification.json').write_bytes(payload)
    print(payload.decode())
    print('INTEGER_IMAGE_DIAGNOSTIC_VERIFIED COLD_SEAL=0 REPORT_SHA256=' + C.sha(payload))


if __name__ == '__main__':
    main()
