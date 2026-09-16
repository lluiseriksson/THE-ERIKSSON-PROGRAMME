"""Synthetic fail-closed checks; not mathematical evidence."""
import copy
import json
from pathlib import Path
import subprocess
import verify_neumann_boundary_orbit_diagnostic as v


def blob(ref, path):
    return subprocess.check_output(['git', 'cat-file', 'blob', ref+':'+path])


def main():
    files = {
        'runner.py': blob('3f9e88f70', 'scripts/colab_neumann_boundary_orbit_diagnostic.py'),
        'durable-base.py': blob('ddf6fdc1882edddbf063389aab4d455a8ed30801',
            'scripts/colab_cmp99_full_green_arbitrary_residue_cold.py'),
        'axiom-gate.py': blob(v.SOURCE, 'scripts/full_green_owner_exact_axiom_gate.py')}
    records = []
    for stage in v.REQUIRED:
        text = ''
        if stage == 'head': text = v.SOURCE
        if stage == 'mathlib_pin': text = v.MATHLIB
        if stage in ('lean_version', 'lake_version'): text = '4.29.0-rc6'
        if stage == 'orbit_repro':
            text = '\n'.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in v.NAMES[stage])
        files[stage+'.log'] = text.encode()
        command = v.COMMANDS.get(stage, ['synthetic', stage])
        if stage == 'checkout': command = ['git','checkout','--detach',v.SOURCE]
        record = dict(stage=stage,command=command,cwd=v.ROOT,exit=0,
            seconds=0.01,timed_out=False,timeout_seconds=120 if stage in v.NAMES else 3600,
            log_file=stage+'.log',output_sha256=v.sha(files[stage+'.log']))
        records.append(record)
        files[stage+'.json'] = json.dumps(record).encode()
    for path in v.PINS: files[Path(path).name] = blob(v.SOURCE,path)
    name = 'NeumannBoundaryOrbitPermutationRepro.olean'
    files[name] = b'synthetic-not-compiler-output'
    contract = dict(source=v.SOURCE,revision=v.REV,scope=v.SCOPE,cold_seal=False,
        pins=v.PINS,names=v.NAMES,queue=[[s,c,v.NAMES.get(s)] for s,c in v.COMMANDS.items()],
        base='ddf6fdc1882edddbf063389aab4d455a8ed30801',base_hash=v.BASE_HASH,
        gate_hash=v.GATE_HASH,outputs={name:v.sha(files[name])})
    files['orbit-diagnostic-contract.json'] = json.dumps(contract).encode()
    data = dict(status='PASS',source_sha=v.SOURCE,runner_rev=v.REV,
        mathlib_sha=v.MATHLIB,toolchain_asset_sha256=v.ASSET,source_blobs=v.PINS,
        minimum_ram_gib=40.0,gpu_runtime_authorized=False,records=records)
    files['evidence.json'] = json.dumps(data).encode()
    files['gate-contract.json'] = json.dumps(dict(source_sha=v.SOURCE,
        project_build_cache_restored=False,expected_axiom_names=v.NAMES['orbit_repro'],
        base_runner_sha256='2f097a374361bd8e4c0f53220ffeeeb22fc06d6ccca5179aebda468d1aebee8e')).encode()
    files['preflight.json'] = json.dumps([dict(actual_exit=x,expected_exit=x,seconds=0.01) for x in (0,7)]).encode()
    v.verify(files)
    bads = []
    bad = dict(files); bad[name] += b'corrupt'; bads.append(bad)
    bad = dict(files); bad['runner.py'] += b'corrupt'; bads.append(bad)
    for change in ('exit', 'prerequisite', 'axiom'):
        bad = dict(files); d = copy.deepcopy(data)
        rec = next(r for r in d['records'] if r['stage']=='orbit_repro')
        if change == 'exit': rec['exit'] = 1
        elif change == 'prerequisite':
            d['records'] = [r for r in d['records'] if r['stage']!='orbit_prerequisite']
        else:
            bad['orbit_repro.log'] = bad['orbit_repro.log'].replace(b'Quot.sound',b'sorryAx')
            rec['output_sha256'] = v.sha(bad['orbit_repro.log'])
        bad['orbit_repro.json'] = json.dumps(rec).encode()
        bad['evidence.json'] = json.dumps(d).encode(); bads.append(bad)
    for bad in bads:
        try: v.verify(bad)
        except (ValueError, RuntimeError, KeyError): continue
        raise AssertionError('CORRUPTION_ACCEPTED')
    print('ORBIT_DIAGNOSTIC_READER_SELF_TEST=PASS synthetic=1 rejected=5')


if __name__ == '__main__': main()
