"""One bounded diagnostic, not a promoted cold seal; retain for HOT repair.

The exact leaf repro precedes the generated physical dependency graph.
All children and axiom outputs are recorded at execution, never tail-parsed.
No credentials, CI, project build cache restoration, or Windows Lean.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import shutil
import types
import urllib.request

SOURCE = 'dc00d3fe4a583da601820605a98644e1fbc0245d'
BASE_SHA = 'ddf6fdc1882edddbf063389aab4d455a8ed30801'
REV = 'neumann-generated-counting-reflection-diagnostic-v1'
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
BLOBS = {
    'tmp/NeumannGeneratedCountingMassReflectionRepro.lean':
        '4af89b1e7ca169aded4bb22e395d7d6dc291f5dffba44ee0c7328444013eaa4a',
    'tmp/NeumannGeneratedCountingMassReflectionDraft.lean':
        '2cd7378c983dfb2f08da54fe4d3c9ce333b0a630f05630c52bf52e66586e3aed',
}
NAMES = {
    'counting_reflection_repro': frozenset({
        'YangMills.RG.neumannCountingReflection_cast_repro',
        'YangMills.RG.neumannCountingReflection_if_repro'}),
    'counting_reflection_draft': frozenset({
        'YangMills.RG.neumannGeneratedFullSiteReflectionDraft_involutive',
        'YangMills.RG.neumannGeneratedTerminalOwner_reflection_draft',
        'YangMills.RG.neumannGeneratedFullCountingMass_reflection_draft'}),
}


def load(sha, path, expected, name):
    url = RAW + sha + '/' + path
    with urllib.request.urlopen(url, timeout=60) as response:
        blob = response.read()
    if hashlib.sha256(blob).hexdigest() != expected:
        raise RuntimeError('TRANSPORT_HASH_MISMATCH=' + path)
    print('TRANSPORT_OK=' + path + ' SHA256=' + expected, flush=True)
    module = types.ModuleType(name)
    exec(compile(blob, url, 'exec'), module.__dict__)
    return module


def main():
    base = load(BASE_SHA, 'scripts/colab_cmp99_full_green_arbitrary_residue_cold.py',
        '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892',
        'counting_reflection_durable_base')
    gate = load(SOURCE, 'scripts/full_green_owner_exact_axiom_gate.py',
        '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
        'counting_reflection_exact_gate')
    runner = base.runner
    runner.RUNNER_REV = REV
    runner.SOURCE_SHA = SOURCE
    base.SOURCE = SOURCE
    runner.ROOT = Path('/content/hrpoly-' + REV)
    runner.EVIDENCE = Path(str(runner.ROOT) + '-evidence')
    runner.ARCHIVE = Path(str(runner.EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(runner.ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = BLOBS
    base.EXPECTED = frozenset().union(*NAMES.values())
    runner.QUEUE = [
        ('geometry_leaf', ['lake', 'build', 'YangMills.RG.NeumannHalfCellBlockReflection'], None),
        ('counting_reflection_repro', ['lake', 'env', 'lean', '-o',
            str(runner.EVIDENCE / 'NeumannGeneratedCountingMassReflectionRepro.olean'),
            'tmp/NeumannGeneratedCountingMassReflectionRepro.lean'], NAMES['counting_reflection_repro']),
        ('physical_prerequisites', ['lake', 'build',
            'YangMills.RG.BalabanCMP99SourceFlatGeneratedTerminalBlockCollapse',
            'YangMills.RG.BalabanCMP99SourceActiveRegionFullCompanion'], None),
        ('counting_reflection_draft', ['lake', 'env', 'lean', '-o',
            str(runner.EVIDENCE / 'NeumannGeneratedCountingMassReflectionDraft.olean'),
            'tmp/NeumannGeneratedCountingMassReflectionDraft.lean'], NAMES['counting_reflection_draft']),
    ]
    axiom_records = {}

    def parse_axioms(output, expected):
        try:
            result = gate.exact_axioms(output, expected)
        except ValueError as error:
            raise RuntimeError(str(error)) from error
        for stage, names in NAMES.items():
            if names == expected:
                axiom_records[stage] = result
        print('AXIOM_GATE=PASS ' + json.dumps(result, sort_keys=True), flush=True)

    runner.parse_axioms = parse_axioms
    base.parse_axioms = parse_axioms
    previous = runner.make_evidence

    def make_evidence(status, opened):
        runner.EVIDENCE.mkdir(parents=True, exist_ok=True)
        outputs = {}
        for name in ('NeumannGeneratedCountingMassReflectionRepro.olean',
                     'NeumannGeneratedCountingMassReflectionDraft.olean'):
            path = runner.EVIDENCE / name
            if path.is_file():
                outputs[name] = hashlib.sha256(path.read_bytes()).hexdigest()
        if status == 'PASS':
            if set(axiom_records) != set(NAMES) or len(outputs) != 2:
                raise RuntimeError('INCOMPLETE_SUCCESS_EVIDENCE')
            if [r['stage'] for r in runner.RECORDS[-4:]] != [q[0] for q in runner.QUEUE]:
                raise RuntimeError('QUEUE_RECORD_MISMATCH')
            if any(r['exit'] != 0 for r in runner.RECORDS):
                raise RuntimeError('NONZERO_CHILD_IN_PASS')
        for path in BLOBS:
            origin = runner.ROOT / path
            if origin.is_file():
                shutil.copyfile(origin, runner.EVIDENCE / origin.name)
        (runner.EVIDENCE / 'diagnostic-contract.json').write_text(json.dumps({
            'source_sha': SOURCE, 'revision': REV, 'cold_seal': False,
            'project_build_cache_restored': False,
            'scope': 'full flat generated counting-mass probes only; not regional inverse or window15',
            'source_blobs': BLOBS,
            'expected_axioms': {k: sorted(v) for k, v in NAMES.items()},
            'recorded_axioms': axiom_records, 'outputs': outputs,
            'queue': [q[0] for q in runner.QUEUE],
        }, sort_keys=True) + '\n', encoding='utf-8')
        return previous(status, opened)

    runner.make_evidence = make_evidence
    if any(p.exists() for p in (runner.ROOT, runner.EVIDENCE, runner.ARCHIVE)):
        raise RuntimeError('ALREADY_STARTED_NO_REEXECUTION')
    gate.self_test()
    base.PREFLIGHT = base.preflight()
    from google.colab import runtime
    saved = runtime.unassign
    runtime.unassign = lambda: print('RUNTIME_RETAINED_FOR_BOUNDED_HOT_REPAIR_AND_EVIDENCE=1', flush=True)
    try:
        return runner.main()
    finally:
        runtime.unassign = saved


if __name__ == '__main__':
    raise SystemExit(main())
