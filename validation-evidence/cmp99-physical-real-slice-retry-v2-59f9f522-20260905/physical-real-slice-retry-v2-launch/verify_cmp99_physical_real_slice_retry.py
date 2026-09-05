"""Read-only v2 diagnostic package verifier. No Lean, Git or subprocesses.

PASS proves the four draft checks only, never a promoted physical cold seal.
FAIL evidence is accepted only as a checked execution prefix.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import math
from pathlib import Path
import types

HELPERS = {
    'colab_cmp99_physical_real_slice_retry.py':
        '968ecbb45914a88114fcf341280c3e52594bf4872bed010d68fc3225d06b7846',
    'verify_cmp99_full_green_residue_cold.py':
        '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
    'full_green_owner_exact_axiom_gate.py':
        '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
}
BOOT = ['download_toolchain', 'extract_toolchain', 'lean_version', 'lake_version',
        'clone', 'checkout', 'head', 'overlay_text_guard', 'import_prefix_guard',
        'lake_update', 'mathlib_pin', 'cache_get']


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def load(folder, name):
    data = (folder / name).read_bytes()
    require(sha(data) == HELPERS[name], 'HELPER_HASH=' + name)
    module = types.ModuleType(name)
    exec(compile(data, name, 'exec'), module.__dict__)
    return module


def verify(files, spec, old, gate):
    data = json.loads(files['evidence.json'])
    for field, value in dict(source_sha=spec.SOURCE, runner_rev=spec.REV,
        source_blobs=spec.BLOBS, mathlib_sha=old.MATHLIB,
        toolchain_asset_sha256=old.ASSET, minimum_ram_gib=40.0,
        gpu_runtime_authorized=False).items():
        require(data.get(field) == value, 'FIELD=' + field)
    status = data.get('status')
    require(status in ('PASS', 'FAIL'), 'STATUS')
    contract = json.loads(files['physical-retry-contract.json'])
    for field, value in dict(source=spec.SOURCE, revision=spec.REV,
        cold_seal=False, project_build_cache_restored=False,
        wrapper_sha256=spec.BASE_HASH, axiom_gate_sha256=spec.GATE_HASH,
        queue=spec.COMMANDS, expected_axioms=sorted(spec.NAMES),
        prior_fail_archive='15017c71e8b58582af23503bfde8b414af00fdddd1a097bd1eb417df8cbbf620').items():
        require(contract.get(field) == value, 'CONTRACT=' + field)
    base = json.loads(files['gate-contract.json'])
    require(base.get('source_sha') == spec.SOURCE and
        base.get('base_runner_sha256') == old.BASE and
        base.get('project_build_cache_restored') is False and
        base.get('expected_axiom_names') == sorted(spec.NAMES), 'BASE_CONTRACT')
    preflight = json.loads(files['preflight.json'])
    require(len(preflight) == 2, 'PREFLIGHT_COUNT')
    for r, code in zip(preflight, (0, 7)):
        require(r['actual_exit'] == r['expected_exit'] == code and
            math.isfinite(r['seconds']) and r['seconds'] >= 0, 'PREFLIGHT')
    records = data['records']
    names = [r['stage'] for r in records]
    required = BOOT + list(spec.COMMANDS)
    filtered = [s for s in names if s not in ('apt_update', 'install_zstd')]
    require(len(names) == len(set(names)), 'DUPLICATE_STAGE')
    require(filtered == required[:len(filtered)], 'STAGE_PREFIX')
    require(set(names) <= set(required) | {'apt_update', 'install_zstd'}, 'EXTRA_STAGE')
    if status == 'PASS':
        require(filtered == required, 'PASS_INCOMPLETE')
    expected_files = {'evidence.json', 'gate-contract.json', 'preflight.json',
                      'physical-retry-contract.json'}
    indexed = {}
    for i, r in enumerate(records):
        s = r['stage']; indexed[s] = r
        require(type(r['exit']) is int, 'EXIT_TYPE')
        require(r['exit'] == 0 or (status == 'FAIL' and i == len(records)-1), 'EXIT_PREFIX')
        require(isinstance(r['seconds'], (int, float)) and
                math.isfinite(r['seconds']) and r['seconds'] >= 0, 'TIME')
        require(r['log_file'] == s+'.log' and sha(files[s+'.log']) == r['output_sha256'], 'LOG_HASH='+s)
        require(json.loads(files[s+'.json']) == r, 'RECORD='+s)
        expected_files |= {s+'.log', s+'.json'}
        if s in spec.COMMANDS:
            require(r['command'] == spec.COMMANDS[s] and r['cwd'] == str(spec.ROOT), 'COMMAND='+s)
        if s == 'checkout':
            require(r['command'] == ['git', 'checkout', '--detach', spec.SOURCE], 'CHECKOUT')
    for s, value in [('head', spec.SOURCE), ('mathlib_pin', old.MATHLIB)]:
        if s in indexed and indexed[s]['exit'] == 0:
            require(files[s+'.log'].decode().strip() == value, 'PIN='+s)
    for s in ('lean_version', 'lake_version'):
        if s in indexed and indexed[s]['exit'] == 0:
            require('4.29.0-rc6' in files[s+'.log'].decode(), 'VERSION='+s)
    present = contract['present_outputs']
    success = contract['successful_outputs']
    require(set(present) <= set(spec.OUTPUTS.values()), 'EXTRA_OUTPUT')
    require(set(success) <= set(present), 'SUCCESS_OUTPUT_SET')
    for name, digest in present.items():
        require(sha(files[name]) == digest, 'OUTPUT_HASH='+name)
        expected_files.add(name)
    for stage, name in spec.OUTPUTS.items():
        if name in success:
            require(stage in indexed and indexed[stage]['exit'] == 0 and
                success[name] == present[name], 'SUCCESS_OUTPUT='+name)
        if status == 'PASS':
            require(name in success, 'PASS_OUTPUT_MISSING='+name)
    require(set(files) == expected_files, 'FILE_SET')
    axioms = contract['actual_axioms']
    if status == 'PASS' or axioms:
        require('physical_real_slice_draft' in indexed and
            indexed['physical_real_slice_draft']['exit'] == 0, 'AXIOM_STAGE')
        actual = gate.exact_axioms(files['physical_real_slice_draft.log'].decode(), spec.NAMES)
        require(axioms == actual, 'AXIOM_RECORD')
    return dict(status=status, cold_seal=False, source=spec.SOURCE,
        stages=len(records), public_axioms=len(axioms), outputs=success,
        queue=[r for r in records if r['stage'] in spec.COMMANDS])


def self_test(spec, old, gate):
    # Synthetic metadata, not Lean evidence. Failures recompute log hashes so
    # exact axiom/command checks, not just integrity hashes, must reject them.
    files = {'preflight.json': json.dumps([dict(actual_exit=n, expected_exit=n,
        seconds=.01) for n in (0,7)]).encode()}
    records = []
    for stage in BOOT + list(spec.COMMANDS):
        text = 'SYNTHETIC_NOT_LEAN'
        if stage == 'head': text = spec.SOURCE
        if stage == 'mathlib_pin': text = old.MATHLIB
        if stage in ('lean_version','lake_version'): text = '4.29.0-rc6'
        if stage == 'physical_real_slice_draft':
            text = '\n'.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]" for n in sorted(spec.NAMES))
        files[stage+'.log'] = text.encode()
        cmd = spec.COMMANDS.get(stage, [])
        if stage == 'checkout': cmd = ['git','checkout','--detach',spec.SOURCE]
        r = dict(stage=stage,exit=0,seconds=.01,log_file=stage+'.log',
            output_sha256=sha(text.encode()),command=cmd,cwd=str(spec.ROOT))
        records.append(r); files[stage+'.json'] = json.dumps(r).encode()
    outputs = {name: sha(b'SYNTHETIC_NOT_LEAN') for name in spec.OUTPUTS.values()}
    for name in outputs: files[name] = b'SYNTHETIC_NOT_LEAN'
    data = dict(source_sha=spec.SOURCE,runner_rev=spec.REV,source_blobs=spec.BLOBS,
        mathlib_sha=old.MATHLIB,toolchain_asset_sha256=old.ASSET,minimum_ram_gib=40.0,
        gpu_runtime_authorized=False,status='PASS',records=records)
    files['evidence.json'] = json.dumps(data).encode()
    files['gate-contract.json'] = json.dumps(dict(source_sha=spec.SOURCE,
        base_runner_sha256=old.BASE,project_build_cache_restored=False,
        expected_axiom_names=sorted(spec.NAMES))).encode()
    contract = dict(source=spec.SOURCE,revision=spec.REV,cold_seal=False,
        project_build_cache_restored=False,wrapper_sha256=spec.BASE_HASH,
        axiom_gate_sha256=spec.GATE_HASH,queue=spec.COMMANDS,expected_axioms=sorted(spec.NAMES),
        actual_axioms=gate.exact_axioms(files['physical_real_slice_draft.log'].decode(),spec.NAMES),
        present_outputs=outputs,successful_outputs=outputs,
        prior_fail_archive='15017c71e8b58582af23503bfde8b414af00fdddd1a097bd1eb417df8cbbf620')
    files['physical-retry-contract.json'] = json.dumps(contract).encode()
    verify(files,spec,old,gate)
    bads = []
    for field,value in [('source_sha','wrong'),('status','INCOMPLETE')]:
        bad=dict(files); d=copy.deepcopy(data); d[field]=value
        bad['evidence.json']=json.dumps(d).encode(); bads.append(bad)
    for filename in ('head.log',next(iter(outputs))):
        bad=dict(files); bad[filename]+=b'corrupt'; bads.append(bad)
    for word in ('sorryAx','ofReduceBool','Other.axiom'):
        bad=dict(files); d=copy.deepcopy(data)
        s='physical_real_slice_draft'; bad[s+'.log']=bad[s+'.log'].replace(b'Quot.sound',word.encode())
        r=next(r for r in d['records'] if r['stage']==s); r['output_sha256']=sha(bad[s+'.log'])
        bad[s+'.json']=json.dumps(r).encode(); bad['evidence.json']=json.dumps(d).encode(); bads.append(bad)
    for bad in bads:
        try: verify(bad,spec,old,gate)
        except (ValueError,RuntimeError): continue
        raise ValueError('SYNTHETIC_NEGATIVE_ACCEPTED')
    # The measured failure shape: bootstrap and repro only, no physical target.
    fail=dict(files); d=copy.deepcopy(data); d['status']='FAIL'
    d['records']=d['records'][:len(BOOT)+1]; d['records'][-1]['exit']=1
    keep={'evidence.json','preflight.json','gate-contract.json','physical-retry-contract.json'}
    for r in d['records']:
        keep|={r['stage']+'.log',r['stage']+'.json'}
        fail[r['stage']+'.json']=json.dumps(r).encode()
    fail={k:v for k,v in fail.items() if k in keep}
    fail['evidence.json']=json.dumps(d).encode()
    c=copy.deepcopy(contract); c.update(actual_axioms={},present_outputs={},successful_outputs={})
    fail['physical-retry-contract.json']=json.dumps(c).encode()
    verify(fail,spec,old,gate)
    print('PHYSICAL_RETRY_VERIFIER_SELF_TEST=PASS synthetic=1 rejected=7 fail_prefix=1')


def main():
    p=argparse.ArgumentParser(); p.add_argument('--helpers',type=Path,required=True)
    p.add_argument('--self-test',action='store_true'); p.add_argument('--archive',type=Path)
    p.add_argument('--sha256'); args=p.parse_args()
    spec=load(args.helpers,'colab_cmp99_physical_real_slice_retry.py')
    old=load(args.helpers,'verify_cmp99_full_green_residue_cold.py')
    gate=load(args.helpers,'full_green_owner_exact_axiom_gate.py')
    if args.self_test: self_test(spec,old,gate); return
    require(args.archive is not None and args.sha256,'ARCHIVE_REQUIRED')
    old.PREFIX=spec.EVIDENCE.name
    report=verify(old.read_archive(args.archive,args.sha256),spec,old,gate)
    print(json.dumps(report,sort_keys=True,indent=2))
    print('PHYSICAL_RETRY_PACKAGE_VERIFIED COLD_SEAL=0')


if __name__ == '__main__': main()
