"""Independent, read-only diagnostic evidence check. No compiler or network.

PASS here never retires PRE-VALIDATION. The exact full-carrier probe result
is not a regional inverse. Every successful child, log, axiom and output is
checked; failed attempts remain evidence of failure, not successful prefixes.
"""
import argparse
import copy
import hashlib
import io
import json
import math
from pathlib import Path, PurePosixPath
import tarfile
import types

SOURCE = '06a928178b22c42c4ecc5387461b808ee3a19dea'
REV = 'neumann-generated-counting-reflection-diagnostic-v2'
ROOT = '/content/hrpoly-' + REV
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
RUNNER_HASH = '4f985fdb7e65c32dee72a71e81e85b1f2d8a97553ca9758bc34934679d862b5d'
MATHLIB = '07642720480157414db592fa85b626dafb71355b'
ASSET = 'bf3e0a4025e47a0bea9ed907d12dcccd3d3590b1d8ad6c55a915298b01ad9d3e'
BLOBS = {
    'tmp/NeumannGeneratedCountingMassReflectionRepro.lean': '4af89b1e7ca169aded4bb22e395d7d6dc291f5dffba44ee0c7328444013eaa4a',
    'tmp/NeumannGeneratedCountingMassReflectionDraft.lean': '5f6edb3c6c7613d59d57cd943b7f9a20af23e3f2f6fe10a5643f696b0cb86fa9',
}
NAMES = {
    'counting_reflection_repro': {'YangMills.RG.neumannCountingReflection_cast_repro',
        'YangMills.RG.neumannCountingReflection_if_repro'},
    'counting_reflection_draft': {'YangMills.RG.neumannGeneratedFullSiteReflectionDraft_involutive',
        'YangMills.RG.neumannGeneratedTerminalOwner_reflection_draft',
        'YangMills.RG.neumannGeneratedFullCountingMass_reflection_draft'},
}
COMMANDS = {
    'geometry_leaf': ['lake', 'build', 'YangMills.RG.NeumannHalfCellBlockReflection'],
    'counting_reflection_repro': ['lake', 'env', 'lean', '-o', ROOT + '-evidence/NeumannGeneratedCountingMassReflectionRepro.olean', 'tmp/NeumannGeneratedCountingMassReflectionRepro.lean'],
    'physical_prerequisites': ['lake', 'build', 'YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse', 'YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanion'],
    'counting_reflection_draft': ['lake', 'env', 'lean', '-o', ROOT + '-evidence/NeumannGeneratedCountingMassReflectionDraft.olean', 'tmp/NeumannGeneratedCountingMassReflectionDraft.lean'],
}
REQUIRED = ['download_toolchain', 'extract_toolchain', 'lean_version', 'lake_version',
    'clone', 'checkout', 'head', 'overlay_text_guard', 'import_prefix_guard',
    'lake_update', 'mathlib_pin', 'cache_get', *COMMANDS]


def require(ok, label):
    if not ok:
        raise ValueError(label)


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def unpack(blob):
    require(len(blob) <= 64 * 2**20, 'ARCHIVE_SIZE')
    files, seen, total = {}, set(), 0
    with tarfile.open(fileobj=io.BytesIO(blob), mode='r:gz') as archive:
        for member in archive:
            p = PurePosixPath(member.name)
            require(not p.is_absolute() and '..' not in p.parts and '\\' not in member.name, 'UNSAFE_PATH')
            require(member.name not in seen, 'DUPLICATE_MEMBER')
            seen.add(member.name)
            require(len(seen) <= 512, 'MEMBER_LIMIT')
            require(member.isdir() or member.isfile(), 'LINK_OR_SPECIAL_MEMBER')
            if member.isdir():
                continue
            total += member.size
            require(0 <= member.size <= 32 * 2**20 and total <= 64 * 2**20, 'EXPANSION_LIMIT')
            files[member.name] = archive.extractfile(member).read()
    return files


def verify_inner(files, gate):
    data = json.loads(files['evidence.json'])
    for key, value in dict(source_sha=SOURCE, runner_rev=REV, status='PASS',
            source_blobs=BLOBS, mathlib_sha=MATHLIB, toolchain_asset_sha256=ASSET,
            minimum_ram_gib=40.0, gpu_runtime_authorized=False).items():
        require(data.get(key) == value, 'EVIDENCE_FIELD=' + key)
    contract = json.loads(files['diagnostic-contract.json'])
    for key, value in dict(source_sha=SOURCE, revision=REV, cold_seal=False,
            project_build_cache_restored=False, source_blobs=BLOBS,
            expected_axioms={k: sorted(v) for k, v in NAMES.items()},
            queue=list(COMMANDS)).items():
        require(contract.get(key) == value, 'CONTRACT_FIELD=' + key)
    base = json.loads(files['gate-contract.json'])
    require(base['source_sha'] == SOURCE and base['project_build_cache_restored'] is False,
        'BASE_CONTRACT')
    require(base['base_runner_sha256'] == '2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e', 'BASE_HASH')
    require(base['expected_axiom_names'] == sorted(set.union(*NAMES.values())), 'BASE_NAMES')
    stages = [r['stage'] for r in data['records']]
    require(len(stages) == len(set(stages)), 'DUPLICATE_STAGE')
    require([s for s in stages if s in REQUIRED] == REQUIRED, 'STAGE_ORDER')
    require(set(stages) <= set(REQUIRED) | {'apt_update', 'install_zstd'}, 'EXTRA_STAGE')
    indexed = {}
    for record in data['records']:
        s = record['stage']
        indexed[s] = record
        require(record['exit'] == 0, 'NONZERO_CHILD=' + s)
        require(math.isfinite(record['seconds']) and record['seconds'] >= 0, 'TIME=' + s)
        require(record['log_file'] == s + '.log', 'LOG_NAME=' + s)
        require(sha(files[s + '.log']) == record['output_sha256'], 'LOG_HASH=' + s)
        require(json.loads(files[s + '.json']) == record, 'RECORD=' + s)
    for stage, command in COMMANDS.items():
        require(indexed[stage]['command'] == command and indexed[stage]['cwd'] == ROOT,
            'COMMAND=' + stage)
    require(indexed['checkout']['command'] == ['git', 'checkout', '--detach', SOURCE], 'CHECKOUT')
    require(files['head.log'].decode().strip() == SOURCE, 'HEAD')
    require(files['mathlib_pin.log'].decode().strip() == MATHLIB, 'MATHLIB')
    for stage in ('lean_version', 'lake_version'):
        require('4.29.0-rc6' in files[stage + '.log'].decode(), 'VERSION=' + stage)
    preflight = json.loads(files['preflight.json'])
    require(len(preflight) == 2, 'PREFLIGHT_COUNT')
    for r, code in zip(preflight, (0, 7)):
        require(r['expected_exit'] == r['actual_exit'] == code and
            math.isfinite(r['seconds']) and r['seconds'] >= 0, 'PREFLIGHT_EXIT_TIMER')
    for name, digest in BLOBS.items():
        require(sha(files[PurePosixPath(name).name]) == digest, 'SOURCE_BLOB=' + name)
    expected_outputs = {PurePosixPath(p).stem + '.olean' for p in BLOBS}
    require(set(contract['outputs']) == expected_outputs, 'OUTPUT_SET')
    for name, digest in contract['outputs'].items():
        require(sha(files[name]) == digest, 'OUTPUT_HASH=' + name)
    expected_files = {'evidence.json', 'diagnostic-contract.json',
        'gate-contract.json', 'preflight.json', *expected_outputs,
        *(PurePosixPath(p).name for p in BLOBS),
        *(s + suffix for s in stages for suffix in ('.log', '.json'))}
    require(set(files) == expected_files, 'INNER_FILE_SET')
    audits = {stage: gate.exact_axioms(files[stage + '.log'].decode(), names)
              for stage, names in NAMES.items()}
    require(audits == contract['recorded_axioms'], 'RECORDED_AXIOMS')
    return dict(status='PASS', cold_seal=False, source=SOURCE, stages=len(stages),
        queue=[indexed[s] for s in COMMANDS], axioms=audits, outputs=contract['outputs'])


def self_test(gate):
    """Synthetic metadata checks only; never compiler evidence."""
    global BLOBS
    saved = BLOBS
    try:
        BLOBS = {p: sha(p.encode()) for p in saved}
        files = {PurePosixPath(p).name: p.encode() for p in BLOBS}
        records = []
        for stage in REQUIRED:
            text = 'synthetic output'
            command = COMMANDS.get(stage, ['synthetic', stage])
            if stage == 'head': text = SOURCE
            if stage == 'mathlib_pin': text = MATHLIB
            if stage in ('lean_version', 'lake_version'): text = '4.29.0-rc6'
            if stage == 'checkout': command = ['git', 'checkout', '--detach', SOURCE]
            if stage in NAMES:
                text = '\n'.join("'" + n + "' depends on axioms: [propext,\n Classical.choice, Quot.sound]"
                    for n in sorted(NAMES[stage]))
            files[stage + '.log'] = text.encode()
            r = dict(stage=stage, command=command, cwd=ROOT, seconds=.01, exit=0,
                log_file=stage + '.log', output_sha256=sha(text.encode()))
            records.append(r)
            files[stage + '.json'] = json.dumps(r).encode()
        data = dict(source_sha=SOURCE, runner_rev=REV, status='PASS', source_blobs=BLOBS,
            mathlib_sha=MATHLIB, toolchain_asset_sha256=ASSET, minimum_ram_gib=40.0,
            gpu_runtime_authorized=False, records=records)
        outputs = {}
        for p in BLOBS:
            name = PurePosixPath(p).stem + '.olean'
            files[name] = ('synthetic NOT an olean ' + name).encode()
            outputs[name] = sha(files[name])
        contract = dict(source_sha=SOURCE, revision=REV, cold_seal=False,
            project_build_cache_restored=False, source_blobs=BLOBS,
            expected_axioms={k: sorted(v) for k, v in NAMES.items()}, queue=list(COMMANDS),
            recorded_axioms={s: gate.exact_axioms(files[s + '.log'].decode(), n) for s, n in NAMES.items()},
            outputs=outputs)
        files['evidence.json'] = json.dumps(data).encode()
        files['diagnostic-contract.json'] = json.dumps(contract).encode()
        files['gate-contract.json'] = json.dumps(dict(source_sha=SOURCE,
            project_build_cache_restored=False,
            base_runner_sha256='2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e',
            expected_axiom_names=sorted(set.union(*NAMES.values())))).encode()
        files['preflight.json'] = json.dumps([dict(expected_exit=c, actual_exit=c, seconds=.01)
            for c in (0, 7)]).encode()
        verify_inner(files, gate)
        bads = []
        for field, value in [('status', 'FAIL'), ('source_sha', 'wrong'), ('mathlib_sha', 'wrong')]:
            bad = dict(files); changed = copy.deepcopy(data); changed[field] = value
            bad['evidence.json'] = json.dumps(changed).encode(); bads.append(bad)
        bad = dict(files); bad[next(iter(outputs))] += b'corrupt'; bads.append(bad)
        bad = dict(files); bad['unregistered.log'] = b'extra'; bads.append(bad)
        bad = dict(files); del bad['physical_prerequisites.log']; bads.append(bad)
        for field, value in [('exit', 1), ('seconds', float('nan')), ('command', ['wrong'])]:
            bad = dict(files); changed = copy.deepcopy(data); changed['records'][-1][field] = value
            bad['evidence.json'] = json.dumps(changed).encode()
            bad['counting_reflection_draft.json'] = json.dumps(changed['records'][-1]).encode()
            bads.append(bad)
        for word in (b'sorryAx', b'ofReduceBool', b'Other.axiom'):
            bad = dict(files); changed = copy.deepcopy(data)
            bad['counting_reflection_draft.log'] = bad['counting_reflection_draft.log'].replace(b'Quot.sound', word)
            changed['records'][-1]['output_sha256'] = sha(bad['counting_reflection_draft.log'])
            bad['counting_reflection_draft.json'] = json.dumps(changed['records'][-1]).encode()
            bad['evidence.json'] = json.dumps(changed).encode(); bads.append(bad)
        for bad in bads:
            try:
                verify_inner(bad, gate)
            except (ValueError, KeyError):
                continue
            raise ValueError('BAD_SYNTHETIC_EVIDENCE_ACCEPTED')
        print('COUNTING_DIAGNOSTIC_VERIFIER_SELF_TEST=PASS synthetic=1 rejected=' + str(len(bads)))
    finally:
        BLOBS = saved


def parse_launch(blob):
    """Decode only the v2 notebook's exact terminal serialization.

    Notebook ae6d6bd7b emits a literal backslash-n suffix, not JSON whitespace.
    The bytes remain hashed and preserved unchanged. Accept exactly that suffix
    (or ordinary JSON); reject extra payload, duplicate keys and NaN constants.
    This does not infer a verdict from stdout.
    """
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, 'DUPLICATE_LAUNCH_KEY=' + key)
            result[key] = value
        return result

    def bad_constant(value):
        raise ValueError('NONFINITE_JSON_CONSTANT=' + value)

    text = blob.decode('utf-8')
    if text.endswith(chr(92) + 'n'):
        text = text[:-2]
    return json.loads(text, object_pairs_hook=unique, parse_constant=bad_constant)


def launch_self_test():
    sample = dict(status='PASS', exit=0, cold_seal=False)
    raw = json.dumps(sample).encode()
    literal_suffix = bytes((92, 110))
    for suffix in (b'', bytes((10,)), literal_suffix):
        require(parse_launch(raw + suffix) == sample, 'LAUNCH_CODEC_VALID')
    bads = [raw + b'junk', raw + literal_suffix * 2,
        b'{"exit":0,"exit":1}', b'{"seconds":NaN}', b'{"seconds":Infinity}']
    for blob in bads:
        try:
            parse_launch(blob)
        except ValueError:
            continue
        raise ValueError('BAD_LAUNCH_CODEC_ACCEPTED')
    print('V2_LAUNCH_CODEC_SELF_TEST=PASS rejected=' + str(len(bads)))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--archive', type=Path)
    parser.add_argument('--sha256')
    parser.add_argument('--axiom-helper', type=Path, required=True)
    parser.add_argument('--self-test', action='store_true')
    args = parser.parse_args()
    helper = args.axiom_helper.read_bytes()
    require(sha(helper) == GATE_HASH, 'HELPER_HASH')
    gate = types.ModuleType('trusted_pinned_axiom_gate')
    exec(compile(helper, str(args.axiom_helper), 'exec'), gate.__dict__)
    gate.self_test()
    launch_self_test()
    if args.self_test:
        self_test(gate)
        return
    require(args.archive is not None and args.sha256, 'ARCHIVE_AND_HASH_REQUIRED')
    blob = args.archive.read_bytes()
    require(sha(blob) == args.sha256.lower(), 'OUTER_HASH')
    outer = unpack(blob)
    prefix = REV + '-launch/'
    require(set(outer) == {prefix + 'runner.py', prefix + 'diagnostic.log',
        prefix + 'launch-final-status.json', 'hrpoly-' + REV + '-evidence.tar.gz'}, 'OUTER_FILE_SET')
    require(sha(outer[prefix + 'runner.py']) == RUNNER_HASH, 'RUNNER_HASH')
    launch = parse_launch(outer[prefix + 'launch-final-status.json'])
    for key, value in dict(status='PASS', cold_seal=False, source=SOURCE, revision=REV,
            runner_sha256=RUNNER_HASH, exit=0).items():
        require(launch.get(key) == value, 'LAUNCH_FIELD=' + key)
    require(math.isfinite(launch['seconds']) and launch['seconds'] >= 0, 'LAUNCH_TIME')
    require(sha(outer[prefix + 'diagnostic.log']) == launch['log_sha256'], 'LAUNCH_LOG')
    inner = outer['hrpoly-' + REV + '-evidence.tar.gz']
    require(sha(inner) == launch['inner_sha256'], 'INNER_HASH')
    nested = unpack(inner)
    inner_prefix = 'hrpoly-' + REV + '-evidence/'
    require(all(n.startswith(inner_prefix) for n in nested), 'INNER_PREFIX')
    files = {n[len(inner_prefix):]: b for n, b in nested.items()}
    report = verify_inner(files, gate)
    report.update(outer_sha256=sha(blob), inner_sha256=sha(inner))
    print(json.dumps(report, sort_keys=True, indent=2))
    print('COUNTING_REFLECTION_DIAGNOSTIC_EVIDENCE_VERIFIED COLD_SEAL=0')


if __name__ == '__main__':
    main()
