"""Fresh diagnostic v2: Mathlib repro before the physical graph, no cold seal.

Reuse the pinned durable bootstrap; never change the mathematical source.
All child logs, exits, source hashes and actual draft outputs are preserved.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import types
import urllib.request

SOURCE = '59f9f522f3f731ac8a6270ac5c3ae719b1b201f6'
REV = 'cmp99-physical-real-slice-retry-v2'
BASE_COMMIT = 'ddf6fdc1882edddbf063389aab4d455a8ed30801'
BASE_HASH = '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
ROOT = Path('/content/hrpoly-' + REV)
EVIDENCE = Path(str(ROOT) + '-evidence')
BLOBS = {
    'tmp/SourceFlowPhysicalCarrierRepro.lean':
        'bee7ef1f12f7b6d8ca19d375484f74fd1785bf42c8b0d841fb2f425a18843ac1',
    'tmp/SourceFlowPhysicalGreenRealSliceDraft.lean':
        '9f035ca0aa1240bb29ed82ec39310779f445f03acc4e4667c1df409187909884',
}
NAMES = frozenset('YangMills.RG.' + name for name in (
    'cmp99SourceFlowPhysicalAmbientGreen_ofReal_draft',
    'cmp99SourceFlowPhysicalStep7bFieldEquiv_apply_site_draft',
    'cmp99SourceFlowPhysicalStep7bGreen_ofReal_draft',
    'norm_cmp99SourceFlowPhysicalStep7bGreen_ofReal_apply_draft',
))
OUTPUTS = {
    'mathlib_carrier_repro': 'SourceFlowPhysicalCarrierRepro.olean',
    'physical_real_slice_draft': 'SourceFlowPhysicalGreenRealSliceDraft.olean',
}
COMMANDS = {
    'mathlib_carrier_repro': ['lake', 'env', 'lean', '-o',
        str(EVIDENCE / OUTPUTS['mathlib_carrier_repro']),
        'tmp/SourceFlowPhysicalCarrierRepro.lean'],
    'physical_prerequisites': ['lake', 'build',
        'YangMills.RG.FinitePiLpRealSliceFibreTransport',
        'YangMills.RG.BalabanCMP99SourceSeparatedSourceFlowFlatPhysicalGreenIdentification'],
    'physical_real_slice_draft': ['lake', 'env', 'lean', '-o',
        str(EVIDENCE / OUTPUTS['physical_real_slice_draft']),
        'tmp/SourceFlowPhysicalGreenRealSliceDraft.lean'],
    'final_source_clean': ['git', 'diff', '--exit-code', 'HEAD', '--',
        'YangMills', 'tmp/SourceFlowPhysicalCarrierRepro.lean',
        'tmp/SourceFlowPhysicalGreenRealSliceDraft.lean',
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
    runner.QUEUE = [(s, cmd, NAMES if s == 'physical_real_slice_draft' else None)
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
            prior_fail_archive='15017c71e8b58582af23503bfde8b414af00fdddd1a097bd1eb417df8cbbf620')
        (EVIDENCE / 'physical-retry-contract.json').write_text(
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
