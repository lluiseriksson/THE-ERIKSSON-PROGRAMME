"""Fresh point-probe retry: explicit carrier NeZero repro before project graph.

Reuse the pinned durable bootstrap; never change the mathematical source.
All child logs, exits, source hashes and actual draft outputs are preserved.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import types
import urllib.request

SOURCE = '91cc4dd5d6133e0eb0fc59279d58a71487caa6c7'
REV = 'cmp99-point-probe-retry-v1'
BASE_COMMIT = 'ddf6fdc1882edddbf063389aab4d455a8ed30801'
BASE_HASH = '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
ROOT = Path('/content/hrpoly-' + REV)
EVIDENCE = Path(str(ROOT) + '-evidence')
BLOBS = {
    'tmp/SourceFlowPointProbeRepro.lean':
        '2a5010721c19914ba451a8525fadaccbbf052539b8374c0865a19873dee428b6',
    'tmp/SourceFlowPhysicalPointProbeDraft.lean':
        '51dc207e4ac84952e4b0487e6ea699cb4dea47ddfca0dfbe52d5f7bc0401a955',
}
NAMES = frozenset('YangMills.RG.' + name for name in (
    'cmp99ComplexOuter_singleFinitePiLp_eq_pointSource_draft',
    'cmp99PhysicalStep7b_complexSingle_eq_pointSource_draft',
))
OUTPUTS = {
    'mathlib_point_probe_repro': 'SourceFlowPointProbeRepro.olean',
    'physical_point_probe_draft': 'SourceFlowPhysicalPointProbeDraft.olean',
}
COMMANDS = {
    'mathlib_point_probe_repro': ['lake', 'env', 'lean', '-o',
        str(EVIDENCE / OUTPUTS['mathlib_point_probe_repro']),
        'tmp/SourceFlowPointProbeRepro.lean'],
    'physical_prerequisites': ['lake', 'build',
        'YangMills.RG.FinitePiLpRealSliceFibreTransport',
        'YangMills.RG.BalabanCMP99SourceSeparatedGeneratedFlatPhysicalStep7bCarrier',
        'YangMills.RG.BalabanCMP99FlatComplexFibrePointSourceFourierReconstruction'],
    'physical_point_probe_draft': ['lake', 'env', 'lean', '-o',
        str(EVIDENCE / OUTPUTS['physical_point_probe_draft']),
        'tmp/SourceFlowPhysicalPointProbeDraft.lean'],
    'final_source_clean': ['git', 'diff', '--exit-code', 'HEAD', '--',
        'YangMills', 'tmp/SourceFlowPointProbeRepro.lean',
        'tmp/SourceFlowPhysicalPointProbeDraft.lean',
        'lean-toolchain', 'lake-manifest.json'],
}


def load(commit, filename, expected, name):
    url = RAW + commit + '/scripts/' + filename
    with urllib.request.urlopen(url, timeout=60) as response:
        blob = response.read()
    if hashlib.sha256(blob).hexdigest() != expected:
        raise RuntimeError('TRANSPORT_HASH=' + filename)
    print('TRANSPORT_OK=' + filename + ' SHA256=' + expected, flush=True)
    module = types.ModuleType(name)
    exec(compile(blob, url, 'exec'), module.__dict__)
    return module


def main():
    if ROOT.exists() or EVIDENCE.exists() or Path(str(EVIDENCE)+'.tar.gz').exists():
        raise RuntimeError('ALREADY_STARTED_NO_REEXECUTION')
    base = load(BASE_COMMIT, 'colab_cmp99_full_green_arbitrary_residue_cold.py',
                BASE_HASH, 'physical_retry_durable_base')
    gate = load(SOURCE, 'full_green_owner_exact_axiom_gate.py', GATE_HASH,
                'physical_retry_exact_gate')
    runner = base.runner
    runner.RUNNER_REV, runner.SOURCE_SHA, base.SOURCE = REV, SOURCE, SOURCE
    runner.ROOT, runner.EVIDENCE = ROOT, EVIDENCE
    runner.ARCHIVE = Path(str(EVIDENCE) + '.tar.gz')
    runner.PATH_MANIFEST = Path(str(ROOT) + '-paths.txt')
    runner.SOURCE_BLOBS = BLOBS
    base.EXPECTED = NAMES
    runner.QUEUE = [(s, cmd, NAMES if s == 'physical_point_probe_draft' else None)
                    for s, cmd in COMMANDS.items()]
    actual_outputs, actual_axioms = {}, {}

    def parse_axioms(raw, expected):
        try:
            result = gate.exact_axioms(raw, expected)
        except ValueError as exc:
            raise RuntimeError(str(exc)) from exc
        if expected == NAMES:
            actual_axioms.update(result)
        print('AXIOM_GATE=PASS ' + json.dumps(result, sort_keys=True), flush=True)

    runner.parse_axioms = base.parse_axioms = parse_axioms
    original_run = runner.run

    def run(stage, command, *, cwd=None):
        if stage == 'overlay_text_guard':
            command = command + ['--require-prevalidation']
        raw = original_run(stage, command, cwd=cwd)
        if stage in OUTPUTS:
            path = EVIDENCE / OUTPUTS[stage]
            if not path.is_file():
                raise RuntimeError('OUTPUT_MISSING=' + path.name)
            actual_outputs[path.name] = runner.sha256(path)
        return raw

    runner.run = run
    old_make = runner.make_evidence

    def make_evidence(status, opened):
        EVIDENCE.mkdir(parents=True, exist_ok=True)
        # Failed Lean may leave a partial output: preserve and label it, never
        # silently discard it or call it a successfully compiled artifact.
        present_outputs = {name: runner.sha256(EVIDENCE / name)
            for name in OUTPUTS.values() if (EVIDENCE / name).is_file()}
        contract = dict(source=SOURCE, revision=REV, cold_seal=False,
            project_build_cache_restored=False, wrapper_sha256=BASE_HASH,
            axiom_gate_sha256=GATE_HASH, queue=COMMANDS,
            expected_axioms=sorted(NAMES), actual_axioms=actual_axioms,
            successful_outputs=actual_outputs, present_outputs=present_outputs,
            prior_fail_archive='cea5571fea96a7ce138184cffddbca13dc724a0a1441de06f5f242ab3b79e01a')
        (EVIDENCE / 'point-probe-retry-contract.json').write_text(
            json.dumps(contract, sort_keys=True)+'\n')
        return old_make(status, opened)

    runner.make_evidence = make_evidence
    gate.self_test()
    base.PREFLIGHT = base.preflight()
    from google.colab import runtime
    saved = runtime.unassign
    runtime.unassign = lambda: print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    try:
        return runner.main()
    finally:
        runtime.unassign = saved


if __name__ == '__main__':
    raise SystemExit(main())
