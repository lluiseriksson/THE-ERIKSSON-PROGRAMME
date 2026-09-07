"""Bounded F4 diagnostic: Mathlib-only repro before any project build.

Fresh pinned checkout, no project cache restoration, but diagnostic only:
neither a complete F4 producer nor physical B0/window15 is certified here.
Never rerun this launcher in the same runtime. Preserve the first error.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import math
from pathlib import Path
import tarfile
import types
import urllib.request

SOURCE = '9dafedaa1bfc08daa258c75a41b27672b9087bb8'
REV = 'cmp85-full-green-hybrid-repro-v2'
ROOT = '/content/hrpoly-' + REV
BASE = 'ddf6fdc1882edddbf063389aab4d455a8ed30801'
BASE_HASH = '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
MATHLIB = '07642720480157414db592fa85b626dafb71355b'
ASSET = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
BLOBS = {
    'tmp/FullGreenHybridIntermediateInequalityRepro.lean':
        'c352b60774c400c31f241e1955106558f9e73549e1a533482bfbc95547980c12',
    'tmp/SourceFullGreenHybridAmplitudeDraft.lean':
        '3df28cff61bfd539dacac6e8e3ee18f175f3535f9d93bf12f59f06a6532b3882',
}
COMMANDS = {
    'mathlib_only_repro': ['lake', 'env', 'lean',
        'tmp/FullGreenHybridIntermediateInequalityRepro.lean'],
    'materialize_sealed_imports': ['lake', 'build',
        'YangMills.RG.BalabanCMP85SourceFullGreenScalarFoundations',
        'YangMills.RG.BalabanCMP99PhysicalFullGreenOwnerResidueBound'],
    'hybrid_draft': ['lake', 'env', 'lean', 'tmp/SourceFullGreenHybridAmplitudeDraft.lean'],
}
NAMES = {
    'mathlib_only_repro': {'fullGreenHybridIntermediateInequalityRepro'},
    'hybrid_draft': {'YangMills.RG.cmp85SourceFullGreen_fullBudget_le_hybrid_draft'},
}
REQUIRED = ['download_toolchain', 'extract_toolchain', 'lean_version', 'lake_version',
    'clone', 'checkout', 'head', 'overlay_text_guard', 'import_prefix_guard',
    'lake_update', 'mathlib_pin', 'cache_get', *COMMANDS]
CONTRACT = dict(source_sha=SOURCE, runner_rev=REV, diagnostic_only=True,
    cold_seal=False, parent_cold_seal='a9d03d7be265bebf9bfc6743c3c66bf560382917',
    base_commit=BASE, base_sha256=BASE_HASH, axiom_gate_sha256=GATE_HASH,
    queue=COMMANDS, audit_expected={s: sorted(n) for s, n in NAMES.items()})


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def module(blob, name):
    result = types.ModuleType(name)
    exec(compile(blob, name, 'exec'), result.__dict__)
    return result


def fetch(commit, path, expected):
    url = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/' + commit + '/' + path
    with urllib.request.urlopen(url, timeout=60) as response:
        blob = response.read()
    require(sha(blob) == expected, 'TRANSPORT_HASH=' + path)
    print('TRANSPORT_SHA256=' + expected + ' PATH=' + path, flush=True)
    return blob


def read_archive(path, expected):
    require(sha(path.read_bytes()) == expected.lower(), 'ARCHIVE_HASH')
    files = {}
    with tarfile.open(path, 'r:gz') as archive:
        members = archive.getmembers()
        require(len(members) < 100 and sum(m.size for m in members) < 10_000_000, 'ARCHIVE_SIZE')
        for m in members:
            if m.isdir():
                continue
            parts = m.name.split('/')
            require(m.isfile() and len(parts) == 2 and
                parts[0] == 'hrpoly-' + REV + '-evidence' and
                parts[1] not in ('', '.', '..') and parts[1] not in files, 'ARCHIVE_MEMBER')
            files[parts[1]] = archive.extractfile(m).read()
    return files


def verify(files, gate):
    data = json.loads(files['evidence.json'])
    for key, value in dict(source_sha=SOURCE, runner_rev=REV, status='PASS',
            source_blobs=BLOBS, mathlib_sha=MATHLIB, toolchain_asset_sha256=ASSET,
            minimum_ram_gib=40.0, gpu_runtime_authorized=False).items():
        require(data.get(key) == value, 'FIELD=' + key)
    require(json.loads(files['hybrid-contract.json']) == CONTRACT, 'CONTRACT')
    contract = json.loads(files['gate-contract.json'])
    require(contract['source_sha'] == SOURCE and
        contract['project_build_cache_restored'] is False and
        contract['expected_axiom_names'] == sorted(set.union(*NAMES.values())) and
        contract['base_runner_sha256'] == '2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e', 'BASE_CONTRACT')
    preflight = json.loads(files['preflight.json'])
    require(len(preflight) == 2, 'PREFLIGHT_COUNT')
    for r, code in zip(preflight, (0, 7)):
        require(r['expected_exit'] == r['actual_exit'] == code and
            math.isfinite(r['seconds']) and r['seconds'] >= 0, 'PREFLIGHT')
    records = data['records']
    stages = [r['stage'] for r in records]
    require(len(stages) == len(set(stages)), 'DUPLICATE_STAGE')
    require([s for s in stages if s in REQUIRED] == REQUIRED and
        set(stages) <= set(REQUIRED) | {'apt_update', 'install_zstd'}, 'STAGE_ORDER')
    names = {'evidence.json', 'preflight.json', 'gate-contract.json', 'hybrid-contract.json'}
    indexed = {}
    for r in records:
        s = r['stage']; indexed[s] = r
        require(r['exit'] == 0 and math.isfinite(r['seconds']) and r['seconds'] >= 0, 'CHILD=' + s)
        require(r['log_file'] == s + '.log' and sha(files[s + '.log']) == r['output_sha256'], 'LOG=' + s)
        require(json.loads(files[s + '.json']) == r, 'RECORD=' + s)
        names |= {s + '.log', s + '.json'}
    require(set(files) == names, 'FILE_SET')
    require(files['head.log'].decode().strip() == SOURCE and
        files['mathlib_pin.log'].decode().strip() == MATHLIB, 'PIN_LOG')
    require(indexed['checkout']['command'] == ['git', 'checkout', '--detach', SOURCE], 'CHECKOUT')
    for s in ('lean_version', 'lake_version'):
        require('4.29.0-rc6' in files[s + '.log'].decode(), 'VERSION')
    for s, command in COMMANDS.items():
        require(indexed[s]['command'] == command and indexed[s]['cwd'] == ROOT, 'COMMAND=' + s)
    audits = {s: gate.exact_axioms(files[s + '.log'].decode(), ns) for s, ns in NAMES.items()}
    return dict(status='PASS', diagnostic_only=True, cold_seal=False,
        source_sha=SOURCE, stages_verified=len(records), audits=audits,
        queue=[indexed[s] for s in COMMANDS], evidence_json_file_sha256=sha(files['evidence.json']))


def self_test(gate):
    gate.self_test()
    files = {'hybrid-contract.json': json.dumps(CONTRACT).encode(),
        'gate-contract.json': json.dumps(dict(source_sha=SOURCE,
            project_build_cache_restored=False, expected_axiom_names=sorted(set.union(*NAMES.values())),
            base_runner_sha256='2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e')).encode(),
        'preflight.json': json.dumps([dict(expected_exit=c, actual_exit=c, seconds=.01) for c in (0, 7)]).encode()}
    records = []
    for s in REQUIRED:
        text = 'synthetic only'
        command = COMMANDS.get(s, ['synthetic'])
        if s == 'head': text = SOURCE
        if s == 'mathlib_pin': text = MATHLIB
        if s in ('lean_version', 'lake_version'): text = '4.29.0-rc6'
        if s == 'checkout': command = ['git', 'checkout', '--detach', SOURCE]
        if s in NAMES:
            text = '\n'.join("'" + n + "' depends on axioms: [propext,\n Classical.choice, Quot.sound]" for n in sorted(NAMES[s]))
        files[s + '.log'] = text.encode()
        r = dict(stage=s, exit=0, seconds=.01, log_file=s + '.log',
            output_sha256=sha(text.encode()), command=command, cwd=ROOT)
        records.append(r); files[s + '.json'] = json.dumps(r).encode()
    data = dict(source_sha=SOURCE, runner_rev=REV, status='PASS', source_blobs=BLOBS,
        mathlib_sha=MATHLIB, toolchain_asset_sha256=ASSET, minimum_ram_gib=40.0,
        gpu_runtime_authorized=False, records=records)
    files['evidence.json'] = json.dumps(data).encode()
    verify(files, gate)
    bads = []
    for key, value in [('status', 'FAIL'), ('source_sha', 'wrong')]:
        bad = dict(files); d = copy.deepcopy(data); d[key] = value
        bad['evidence.json'] = json.dumps(d).encode(); bads.append(bad)
    bad = dict(files); bad['head.log'] += b'corrupt'; bads.append(bad)
    bad = dict(files); del bad['mathlib_only_repro.log']; bads.append(bad)
    for word in ('sorryAx', 'ofReduceBool', 'Other.axiom'):
        bad = dict(files); d = copy.deepcopy(data)
        s = 'hybrid_draft'; bad[s + '.log'] = bad[s + '.log'].replace(b'Quot.sound', word.encode())
        d['records'][-1]['output_sha256'] = sha(bad[s + '.log'])
        bad[s + '.json'] = json.dumps(d['records'][-1]).encode()
        bad['evidence.json'] = json.dumps(d).encode(); bads.append(bad)
    for bad in bads:
        try: verify(bad, gate)
        except (ValueError, KeyError, RuntimeError): continue
        raise ValueError('NEGATIVE_FIXTURE_ACCEPTED')
    print('HYBRID_VERIFIER_SELF_TEST=PASS synthetic=1 rejected=' + str(len(bads)), flush=True)


def run():
    base = module(fetch(BASE, 'scripts/colab_cmp99_full_green_arbitrary_residue_cold.py', BASE_HASH), 'hybrid_durable_base')
    gate = module(fetch(SOURCE, 'scripts/full_green_owner_exact_axiom_gate.py', GATE_HASH), 'hybrid_exact_gate')
    self_test(gate)
    runner = base.runner
    runner.RUNNER_REV = REV; runner.SOURCE_SHA = SOURCE; base.SOURCE = SOURCE
    runner.ROOT = Path(ROOT); runner.EVIDENCE = Path(ROOT + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(ROOT + '-paths.txt'); runner.SOURCE_BLOBS = BLOBS
    runner.QUEUE = [(s, command, NAMES.get(s)) for s, command in COMMANDS.items()]
    base.EXPECTED = set.union(*NAMES.values())
    def parse(output, expected):
        try: result = gate.exact_axioms(output, expected)
        except ValueError as error: raise RuntimeError(str(error)) from error
        print('AXIOM_GATE=PASS ' + json.dumps(result, sort_keys=True), flush=True)
    runner.parse_axioms = parse; base.parse_axioms = parse
    previous = runner.make_evidence
    def evidence(status, opened):
        runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
        (runner.EVIDENCE / 'hybrid-contract.json').write_text(json.dumps(CONTRACT, sort_keys=True) + '\n')
        return previous(status, opened)
    runner.make_evidence = evidence
    require(not any(p.exists() for p in (runner.ROOT, runner.EVIDENCE, runner.ARCHIVE)), 'ALREADY_STARTED_NO_REEXECUTION')
    base.PREFLIGHT = base.preflight()
    from google.colab import runtime
    saved = runtime.unassign
    runtime.unassign = lambda: print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    try:
        code = runner.main()
        if code == 0:
            report = verify(read_archive(runner.ARCHIVE, runner.sha256(runner.ARCHIVE)), gate)
            report['archive_sha256'] = runner.sha256(runner.ARCHIVE)
            report_path = Path(ROOT + '-verification.json')
            report_path.write_text(json.dumps(report, sort_keys=True, indent=2) + '\n')
            print('DIAGNOSTIC_PACKAGE_VERIFIED=' + str(report_path), flush=True)
            print('VERIFICATION_SHA256=' + runner.sha256(report_path), flush=True)
        print('DIAGNOSTIC_FINAL_STATUS=' + ('PASS' if code == 0 else 'FAIL') + ' COLD_SEAL=0', flush=True)
        return code
    finally:
        runtime.unassign = saved


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--verify', type=Path); p.add_argument('--sha256')
    p.add_argument('--gate', type=Path); p.add_argument('--self-test', action='store_true')
    args = p.parse_args()
    if args.verify or args.self_test:
        require(args.gate is not None, 'GATE_REQUIRED')
        blob = args.gate.read_bytes(); require(sha(blob) == GATE_HASH, 'GATE_HASH')
        gate = module(blob, 'hybrid_offline_gate')
        if args.self_test: self_test(gate)
        else:
            require(bool(args.sha256), 'EXPECTED_HASH_REQUIRED')
            print(json.dumps(verify(read_archive(args.verify, args.sha256), gate), sort_keys=True, indent=2))
        return 0
    return run()


if __name__ == '__main__':
    try:
        code = main()
    except Exception as error:
        import traceback
        traceback.print_exc()
        print('DIAGNOSTIC_FIRST_ERROR=' + repr(error), flush=True)
        print('DIAGNOSTIC_FINAL_STATUS=FAIL COLD_SEAL=0', flush=True)
        code = 1
    raise SystemExit(code)
