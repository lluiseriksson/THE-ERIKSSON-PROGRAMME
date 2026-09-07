"""Fresh bounded diagnostic of actual coordinate precision conjugacy.

Not a production cold seal. Exact input/output provenance and child exits
are retained; no regional inverse or scalar-window attainment is claimed.
"""
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time
import types
import urllib.request

SOURCE = '95c757465455c7e8cffcfcd6d9d18aa56f6d5083'
REV = 'neumann-coordinate-precision-diagnostic-v1'
RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
BASE = 'ddf6fdc1882edddbf063389aab4d455a8ed30801'
BASE_HASH = '29a5ebd9cba53e5b2d98eecd7dfb90bbf0a52430d8995deaf623e769b6be2892'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
PINS = {
    "tmp/NeumannCoordinateProductRepro.lean": "6b859bd3e4abb7840b577f73d860e9b574c91db341391b59ea308eeff81b5719",
    "tmp/NeumannHalfCellPhaseRepro.lean": "ce9ecdf21529aab7bc4e479a6ff147be1f9d713dccee635589b92e0d594ee7dd",
    "tmp/NeumannEntireAverageHalfCellPhaseDraft.lean": "b7f5c7a3173455ff5681f24fc1657b37657d3c341ea89c9fb7c7f628133c92be",
    "tmp/NeumannCoordinateAliasReflectionDraft.lean": "ffb4bbab01f8f49b593d2f2657f12a499232501a54bb64638c0320c8d28aea3e",
    "tmp/NeumannCoordinateMomentumCarryDraft.lean": "c9ba9baf19e91d6d6ba1c75c3aebfb64fed60c4b5af691f9756ef02f7933252c",
    "tmp/NeumannCoordinateAveragePhaseDraft.lean": "34572ae8bb05d3a2928abd172504ee201b58616e1817ca236283e4c73333d645"
}
NAMES = {
    "product_repro": [
        "NeumannCoordinateProductRepro.one_factor"
    ],
    "half_cell_repro": [
        "NeumannHalfCellPhaseRepro.finite_exp_reverse"
    ],
    "half_cell_physical": [
        "YangMills.RG.neumannEntireAverageFactor_halfCellPhase"
    ],
    "alias_physical": [
        "YangMills.RG.neumannAliasCoordinateReflection_involutive",
        "YangMills.RG.neumannAliasCoordinateReflection_other",
        "YangMills.RG.neumannAliasCoordinateReflection_residue",
        "YangMills.RG.neumannAliasCoordinateReflection_sum",
        "YangMills.RG.neumannAliasPiCoordinateReflection_other",
        "YangMills.RG.neumannAliasPiCoordinateReflection_self",
        "YangMills.RG.neumannPhysicalAliasCoordinateReflection_central"
    ],
    "carry_physical": [
        "YangMills.RG.neumannEntireAliasFineSymbol_coordinateReflection",
        "YangMills.RG.neumannEntireScaledLaplacianSymbol_coordinateReflection",
        "YangMills.RG.neumannMomentumCoordinateReflection_involutive",
        "YangMills.RG.neumannPhysicalAliasCoordinateReflection_momentum"
    ],
    "phase_physical": [
        "YangMills.RG.neumannCoordinateHalfCellPhase_ne_zero",
        "YangMills.RG.neumannCoordinateHalfCellPhase_neg",
        "YangMills.RG.neumannEntireAliasAverageColumn_coordinateReflection",
        "YangMills.RG.neumannEntireAliasAverageRow_coordinateReflection",
        "YangMills.RG.neumannEntireAliasPrecisionMatrix_coordinateReflection",
        "YangMills.RG.neumannEntireAverageAmplitude_coordinateReflection"
    ]
}
SCOPE = 'one-coordinate literal alias precision conjugacy via exact averaging phases; not actual Green covariance, regional inverse, B0 or window15'

def load(ref, path, digest, name):
    url = RAW + ref + '/' + path
    blob = urllib.request.urlopen(url, timeout=60).read()
    assert hashlib.sha256(blob).hexdigest() == digest, 'TRANSPORT_HASH=' + path
    m = types.ModuleType(name)
    exec(compile(blob, url, 'exec'), m.__dict__)
    return m, blob

def main():
    base, base_blob = load(BASE, 'scripts/colab_cmp99_full_green_arbitrary_residue_cold.py', BASE_HASH, 'base')
    gate, gate_blob = load(SOURCE, 'scripts/full_green_owner_exact_axiom_gate.py', GATE_HASH, 'gate')
    r = base.runner
    r.RUNNER_REV, r.SOURCE_SHA, base.SOURCE = REV, SOURCE, SOURCE
    r.ROOT = Path('/content/hrpoly-' + REV)
    r.EVIDENCE = Path(str(r.ROOT) + '-evidence')
    r.ARCHIVE = Path(str(r.EVIDENCE) + '.tar.gz')
    r.PATH_MANIFEST = Path(str(r.ROOT) + '-paths.txt')
    r.SOURCE_BLOBS = PINS
    def run(stage, command, *, cwd=None):
        r.EVIDENCE.mkdir(parents=True, exist_ok=True)
        log = r.EVIDENCE / (stage + '.log')
        limit = 120 if stage in NAMES else 3600
        started, timed_out = time.perf_counter(), False
        print('STAGE=' + stage + ' CMD=' + json.dumps(command), flush=True)
        with log.open('xb') as stream:
            p = subprocess.Popen(command, cwd=cwd, env=os.environ.copy(),
                stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = p.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(p.pid, signal.SIGKILL)
                code = p.wait()
        blob = log.read_bytes()
        record = dict(stage=stage, command=command, cwd=str(cwd) if cwd else None,
            exit=code, seconds=time.perf_counter()-started, timed_out=timed_out,
            timeout_seconds=limit, log_file=log.name,
            output_sha256=hashlib.sha256(blob).hexdigest())
        r.RECORDS.append(record)
        temp = r.EVIDENCE / (stage + '.json.tmp')
        temp.write_text(json.dumps(record, sort_keys=True) + '\n')
        temp.replace(r.EVIDENCE / (stage + '.json'))
        output = blob.decode(errors='replace')
        print(output[-6000:], flush=True)
        print(json.dumps(record, sort_keys=True), flush=True)
        if code != 0 or timed_out:
            raise RuntimeError('FIRST_ERROR=' + stage)
        return output
    r.run = run
    lib = '.lake/build/lib/lean'
    r.QUEUE = [
        ("scratch_import_path", ["python3","-c","from pathlib import Path; Path('.lake/build/lib/lean').mkdir(parents=True, exist_ok=True)"], None),
        ("product_repro", ["lake","env","lean","-o",".lake/build/lib/lean/NeumannCoordinateProductRepro.olean","tmp/NeumannCoordinateProductRepro.lean"], NAMES["product_repro"]),
        ("half_cell_repro", ["lake","env","lean","-o",".lake/build/lib/lean/NeumannHalfCellPhaseRepro.olean","tmp/NeumannHalfCellPhaseRepro.lean"], NAMES["half_cell_repro"]),
        ("physical_prerequisites", ["lake","build","YangMills.RG.BalabanCMP99SourceAliasReflectionInvolutive","YangMills.RG.BalabanCMP99SourceAliasReflectionStabilizedSolution","YangMills.RG.BalabanCMP89Eq251EntireAverageAmplitude"], None),
        ("half_cell_physical", ["lake","env","lean","-o",".lake/build/lib/lean/NeumannEntireAverageHalfCellPhaseDraft.olean","tmp/NeumannEntireAverageHalfCellPhaseDraft.lean"], NAMES["half_cell_physical"]),
        ("alias_physical", ["lake","env","lean","-o",".lake/build/lib/lean/NeumannCoordinateAliasReflectionDraft.olean","tmp/NeumannCoordinateAliasReflectionDraft.lean"], NAMES["alias_physical"]),
        ("carry_physical", ["lake","env","lean","-o",".lake/build/lib/lean/NeumannCoordinateMomentumCarryDraft.olean","tmp/NeumannCoordinateMomentumCarryDraft.lean"], NAMES["carry_physical"]),
        ("phase_physical", ["lake","env","lean","-o",".lake/build/lib/lean/NeumannCoordinateAveragePhaseDraft.olean","tmp/NeumannCoordinateAveragePhaseDraft.lean"], NAMES["phase_physical"]),
        ("clean_after", ["git","diff","--exit-code","HEAD","--","YangMills","tmp/NeumannCoordinateProductRepro.lean","tmp/NeumannHalfCellPhaseRepro.lean","tmp/NeumannEntireAverageHalfCellPhaseDraft.lean","tmp/NeumannCoordinateAliasReflectionDraft.lean","tmp/NeumannCoordinateMomentumCarryDraft.lean","tmp/NeumannCoordinateAveragePhaseDraft.lean","lean-toolchain","lake-manifest.json"], None),
    ]
    base.EXPECTED = frozenset().union(*NAMES.values())
    def parse(output, expected):
        try:
            result = gate.exact_axioms(output, expected)
        except ValueError as e:
            raise RuntimeError(str(e)) from e
        print('AXIOM_GATE=PASS ' + json.dumps(result, sort_keys=True), flush=True)
    r.parse_axioms = base.parse_axioms = parse
    previous = r.make_evidence
    def preserve(status, opened):
        r.EVIDENCE.mkdir(parents=True, exist_ok=True)
        for name, blob in [('runner.py', Path(__file__).read_bytes()), ('durable-base.py', base_blob), ('axiom-gate.py', gate_blob)]:
            (r.EVIDENCE / name).write_bytes(blob)
        outputs = {}
        for name in ["NeumannCoordinateProductRepro","NeumannHalfCellPhaseRepro","NeumannEntireAverageHalfCellPhaseDraft","NeumannCoordinateAliasReflectionDraft","NeumannCoordinateMomentumCarryDraft","NeumannCoordinateAveragePhaseDraft"]:
            f = r.ROOT / lib / (name + '.olean')
            if f.is_file():
                blob = f.read_bytes()
                outputs[f.name] = hashlib.sha256(blob).hexdigest()
                (r.EVIDENCE / f.name).write_bytes(blob)
        for p in PINS:
            f = r.ROOT / p
            if f.is_file():
                (r.EVIDENCE / f.name).write_bytes(f.read_bytes())
        (r.EVIDENCE / 'coordinate-contract.json').write_text(json.dumps(dict(
            source=SOURCE, revision=REV, scope=SCOPE, cold_seal=False,
            pins=PINS, names={k: sorted(v) for k, v in NAMES.items()},
            queue=[(s,c,sorted(n) if n else None) for s,c,n in r.QUEUE], outputs=outputs,
            base=BASE, base_hash=BASE_HASH, gate_hash=GATE_HASH), sort_keys=True) + '\n')
        return previous(status, opened)
    r.make_evidence = preserve
    assert not any(p.exists() for p in (r.ROOT, r.EVIDENCE, r.ARCHIVE)), 'NO_REEXECUTION'
    gate.self_test()
    base.PREFLIGHT = base.preflight()
    from google.colab import runtime
    old = runtime.unassign
    runtime.unassign = lambda: print('RUNTIME_RETAINED_FOR_EVIDENCE=1', flush=True)
    try:
        return r.main()
    finally:
        runtime.unassign = old

if __name__ == '__main__':
    raise SystemExit(main())
