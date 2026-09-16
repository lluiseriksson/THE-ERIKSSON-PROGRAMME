"""Independent bounded archive reader. Rechecks actual cold prior; no Lean/network."""
import argparse
import json
import math
from pathlib import Path
import types

from verify_neumann_counting_reflection_diagnostic_v2 import unpack, require, sha

BASE = '9b73a5fe37d1e5e3c8589af211c46708a9d0a7bb'
SOURCE = 'd7e2199934a14c843d46cb08094c554bc9d0c5f1'
RUNNER = '5089ed064f0ad30556c2bda35576f661a8db6e8f62eb71a288ffdaf007313b8d'
BLOB = '62c8ceb7502820740147bd678955e0ca529cceb6954bb350b4c0fbbcfc46a4d1'
NAME = 'NeumannIntegerImageBlockOwnerRepro.lean'
ROOT = '/content/hrpoly-neumann-counting-promoted-cold-v1'
WORK = '/content/neumann-integer-image-owner-hot-v1'
HELPERS = '/content/neumann-counting-promoted-cold-v1-launch'
PRIOR = ROOT + '-evidence.tar.gz'
INPUT = 'tmp/neumann_integer_image_owner_hot_v1/' + NAME
PINS = {
    'verify_neumann_counting_promoted_cold.py': '9decd5ede386cf72c30c6a1909e545f852a68e8fad4801ba48674adbe0caf5c5',
    'verify_cmp99_full_green_residue_cold.py': '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
    'full_green_owner_exact_axiom_gate.py': '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
}
NAMES = {'neumannIntegerHalfCellOwner_repro',
    'neumannIntegerTranslatedOwner_repro', 'neumannIntegerReflectedOwner_repro'}
STAGES = ['verify_cold_archive', 'base_head', 'mathlib_pin', 'clean_source',
    'lean_version', 'lake_version', 'text_guard', 'import_guard',
    'integer_image_owner_repro', 'final_clean_source']


def check(files, prior_blob):
    data = json.loads(files['evidence.json'])
    prior_hash = sha(prior_blob)
    for key, value in dict(status='PASS', cold_seal=False, base=BASE, source=SOURCE,
            source_blob=BLOB, prior_sha256=prior_hash, error=None).items():
        require(data.get(key) == value, 'FIELD=' + key)
    expected = {'runner.py', NAME, 'records.json', 'paths.txt', 'repro.olean',
        'toolchain-binaries.json', *PINS, *(s + '.log' for s in STAGES)}
    require(set(data['files']) == expected and set(files) == expected | {'evidence.json'}, 'FILES')
    for name, digest in data['files'].items():
        require(sha(files[name]) == digest, 'HASH=' + name)
    for name, digest in dict(PINS, **{'runner.py': RUNNER, NAME: BLOB}).items():
        require(sha(files[name]) == digest, 'PIN=' + name)
    modules = {}
    for name in PINS:
        module = types.ModuleType(name)
        exec(compile(files[name], name, 'exec'), module.__dict__)
        modules[name] = module
    gate = modules['full_green_owner_exact_axiom_gate.py']
    nested = unpack(prior_blob)
    prefix = Path(ROOT).name + '-evidence/'
    require(all(n.startswith(prefix) for n in nested), 'PRIOR_PREFIX')
    cold = modules['verify_neumann_counting_promoted_cold.py'].verify(
        {n[len(prefix):]: b for n, b in nested.items()}, gate,
        modules['verify_cmp99_full_green_residue_cold.py'])
    records = data['records']
    require(records == json.loads(files['records.json']), 'RECORDS')
    require([r['stage'] for r in records] == STAGES, 'ORDER')
    py = records[0]['command'][0]
    require(py in ('/usr/bin/python3', '/usr/local/bin/python3'), 'PYTHON')
    bindir = '/content/lean-4.29.0-rc6-linux/lean-4.29.0-rc6-linux/bin/'
    clean = ['git', 'diff', '--exit-code', 'HEAD', '--', 'YangMills', 'lean-toolchain', 'lake-manifest.json']
    commands = {
        'verify_cold_archive': [py, HELPERS + '/verify_neumann_counting_promoted_cold.py',
            '--helpers', HELPERS, '--archive', PRIOR, '--sha256', prior_hash],
        'base_head': ['git', 'rev-parse', 'HEAD'],
        'mathlib_pin': ['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD'],
        'clean_source': clean, 'final_clean_source': clean,
        'lean_version': [bindir + 'lean', '--version'],
        'lake_version': [bindir + 'lake', '--version'],
        'text_guard': [py, 'scripts/check_lean_overlay_text.py', '--paths-from',
            WORK + '/paths.txt', '--require-prevalidation'],
        'import_guard': [py, 'scripts/check_lean_import_prefix.py', INPUT],
        'integer_image_owner_repro': ['lake', 'env', 'lean', '-o', WORK + '/repro.olean', INPUT],
    }
    for r in records:
        require(r['exit'] == 0 and r['timed_out'] is False, 'CHILD=' + r['stage'])
        require(r['command'] == commands[r['stage']] and r['cwd'] == ROOT, 'COMMAND')
        require(math.isfinite(r['seconds']) and r['seconds'] >= 0, 'TIMER')
        require(sha(files[r['stage'] + '.log']) == r['log_sha256'], 'LOG')
    for name, value in [('base_head.log', BASE), ('paths.txt', INPUT),
            ('mathlib_pin.log', '07642720480157414db592fa85b626dafb71355b')]:
        require(files[name].decode().strip() == value, 'VALUE=' + name)
    for name in ('lean', 'lake'):
        require('4.29.0-rc6' in files[name + '_version.log'].decode(), 'VERSION')
    axioms = gate.exact_axioms(files['integer_image_owner_repro.log'].decode(), NAMES)
    require(axioms == data['axioms'] and len(files['repro.olean']) > 0, 'AXIOMS_OR_OUTPUT')
    return dict(status='PASS', cold_seal=False, source=SOURCE, base=BASE,
        prior_sha256=prior_hash, prior_cold_verification=cold, records=records,
        axioms=axioms, output_sha256=sha(files['repro.olean']))


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--sha256', required=True)
    p.add_argument('--prior-inner', type=Path, required=True)
    p.add_argument('--destination', type=Path)
    a = p.parse_args()
    if a.destination:
        require(not a.destination.exists(), 'NO_OVERWRITE')
    require(a.archive.stat().st_size <= 64 * 2**20 and
        a.prior_inner.stat().st_size <= 64 * 2**20, 'SIZE')
    blob, prior = a.archive.read_bytes(), a.prior_inner.read_bytes()
    require(sha(blob) == a.sha256.lower(), 'OUTER_HASH')
    nested = unpack(blob)
    prefix = Path(WORK).name + '/'
    require(all(n.startswith(prefix) for n in nested), 'PREFIX')
    report = check({n[len(prefix):]: b for n, b in nested.items()}, prior)
    report['outer_sha256'] = sha(blob)
    payload = (json.dumps(report, sort_keys=True, indent=2) + '\n').encode()
    if a.destination:
        a.destination.mkdir(parents=True, exist_ok=False)
        (a.destination / a.archive.name).write_bytes(blob)
        for name, content in nested.items():
            target = a.destination / name
            target.parent.mkdir(parents=True, exist_ok=True)
            with target.open('xb') as out:
                out.write(content)
        (a.destination / 'independent-verification.json').write_bytes(payload)
    print(payload.decode(), end='')
    print('INTEGER_IMAGE_OWNER_HOT_VERIFIED COLD_SEAL=0 REPORT_SHA256=' + sha(payload))


if __name__ == '__main__':
    main()
