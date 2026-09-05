"""Independent bounded archive verifier; no Lean, network or subprocess.

Verifies diagnostic provenance, stage prefix, outputs and exact axiom names.
HOT success is explicitly not a cold seal or a terminal-field discharge.
"""
from __future__ import annotations
import argparse
import copy
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import tarfile
import types

RUNNER_HASH = '8136ae6f543a5725fc6edef230af99d216d6fd8a8556d0b8daabd726170015fa'
GATE_HASH = '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2'
MATHLIB = '07642720480157414db592fa85b626dafb71355b'


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(blob):
    return hashlib.sha256(blob).hexdigest()


def load(path, digest):
    blob = path.read_bytes()
    require(sha(blob) == digest, 'HELPER_HASH=' + path.name)
    module = types.ModuleType(path.stem)
    exec(compile(blob, str(path), 'exec'), module.__dict__)
    return module


def read_archive(path, digest, prefix):
    require(path.stat().st_size <= 32_000_000, 'ARCHIVE_SIZE')
    require(sha(path.read_bytes()) == digest.lower(), 'ARCHIVE_HASH')
    files, total = {}, 0
    with tarfile.open(path, 'r:gz') as tar:
        for member in tar:
            if member.isdir():
                require(member.name.rstrip('/') == prefix, 'DIRECTORY')
                continue
            require(member.isfile() and 0 <= member.size <= 16_000_000, 'MEMBER_KIND_SIZE')
            require(member.name.startswith(prefix+'/'), 'MEMBER_PREFIX')
            name = member.name[len(prefix)+1:]
            require(name and '/' not in name and '\\' not in name and name not in ('.','..'), 'MEMBER_PATH')
            require(name not in files, 'DUPLICATE_MEMBER')
            total += member.size
            require(total <= 64_000_000, 'TOTAL_SIZE')
            files[name] = tar.extractfile(member).read()
    return files


def verify(files, spec, gate, prior_hash):
    data = json.loads(files['evidence.json'])
    require(data['source'] == spec.SOURCE and data['retained_source'] == spec.BASE
            and data['revision'] == spec.REV, 'SOURCE_REVISION')
    require(data['cold_seal'] is False, 'NOT_COLD')
    require(data['prior_archive_sha256'] == prior_hash, 'PRIOR_HASH')
    require(data['source_blobs'] == spec.BLOBS and data['helper_hashes'] == spec.HELPER_HASHES, 'PINS')
    require(data['status'] in ('PASS','FAIL'), 'STATUS')
    require(set(files) == set(data['files']) | {'evidence.json'}, 'FILE_SET')
    for name, digest in data['files'].items():
        require(sha(files[name]) == digest, 'FILE_HASH='+name)
    queue = spec.commands(prior_hash)
    allowed = {'evidence.json','records.json','paths.txt','prior-launch-status.json'}
    allowed |= {PurePosixPath(p).name for p in spec.BLOBS} | set(spec.OUTPUTS.values())
    allowed |= {s+'.log' for s in queue}
    require(set(files) <= allowed, 'UNEXPECTED_FILE')
    records = data['records']
    require(len(records) <= len(queue), 'TOO_MANY_STAGES')
    require([r['stage'] for r in records] == list(queue)[:len(records)], 'STAGE_PREFIX')
    if records:
        require(json.loads(files['records.json']) == records, 'ATOMIC_RECORDS')
    indexed = {r['stage']:r for r in records}
    for i,r in enumerate(records):
        stage = r['stage']
        require(r['command'] == queue[stage] and r['cwd'] == str(spec.ROOT), 'COMMAND='+stage)
        require(r['log'] == stage+'.log', 'LOG_NAME')
        require(type(r['exit']) is int, 'EXIT_TYPE')
        require(type(r['seconds']) in (int,float) and math.isfinite(r['seconds'])
                and r['seconds'] >= 0, 'DURATION')
        require(sha(files[r['log']]) == r['sha256'], 'LOG_HASH')
        require(r['exit'] == 0 or i == len(records)-1, 'CONTINUED_AFTER_ERROR')
    for path,digest in spec.BLOBS.items():
        name = PurePosixPath(path).name
        if name in files:
            require(sha(files[name]) == digest, 'SOURCE_BYTES='+name)
    success, present = data['successful_outputs'], data['present_outputs']
    require(set(present) == set(files) & set(spec.OUTPUTS.values()), 'PRESENT_OUTPUT_SET')
    require(set(success) <= set(present), 'SUCCESS_WITHOUT_OUTPUT')
    for name,digest in present.items():
        require(sha(files[name]) == digest, 'OUTPUT_HASH')
    for stage,name in spec.OUTPUTS.items():
        if name in success:
            require(stage in indexed and indexed[stage]['exit'] == 0, 'OUTPUT_WITHOUT_SUCCESS')
            require(success[name] == present[name], 'SUCCESS_OUTPUT_HASH')
    require(set(data['axioms']) <= set(spec.AXIOMS), 'AXIOM_STAGE_SET')
    for stage,actual in data['axioms'].items():
        require(stage in indexed and indexed[stage]['exit'] == 0, 'AXIOM_WITHOUT_SUCCESS')
        require(gate.exact_axioms(files[stage+'.log'].decode(),spec.AXIOMS[stage]) == actual, 'AXIOM_MAP')
    if data['status'] == 'PASS':
        require(len(records) == len(queue) and all(r['exit'] == 0 for r in records), 'PASS_EXITS')
        require(data['error'] is None, 'PASS_ERROR')
        require(json.loads(files['prior-launch-status.json']) == dict(status='PASS',source=spec.BASE,
            revision='cmp99-physical-prefix-promoted-cold-v1',cold_seal=True), 'PRIOR_STATUS')
        require(files['retained_head.log'].decode().strip() == spec.BASE, 'HEAD_LOG')
        require(files['mathlib_pin.log'].decode().strip() == MATHLIB, 'MATHLIB_LOG')
        require(files['paths.txt'].decode().splitlines() == list(spec.BLOBS), 'PATH_MANIFEST')
        require(all(PurePosixPath(p).name in files for p in spec.BLOBS), 'SOURCE_MISSING')
        require(set(success) == set(spec.OUTPUTS.values()), 'PASS_OUTPUTS')
        require(set(data['axioms']) == set(spec.AXIOMS), 'PASS_AXIOM_STAGES')
    else:
        require(isinstance(data['error'],str) and data['error'], 'FAIL_ERROR')
    return dict(status=data['status'],cold_seal=False,source=spec.SOURCE,
        stages=len(records),public_axioms=sum(map(len,data['axioms'].values())),
        first_error=data['error'],outputs=success)


def self_test(spec, gate):
    # Synthetic fixture ONLY. The original source hashes are restored afterward.
    original = spec.BLOBS
    try:
        source = {PurePosixPath(p).name:('SYNTHETIC '+p).encode() for p in original}
        spec.BLOBS = {p:sha(source[PurePosixPath(p).name]) for p in original}
        prior = '0'*64
        files = dict(source)
        files['paths.txt'] = ('\n'.join(spec.BLOBS)+'\n').encode()
        files['prior-launch-status.json'] = json.dumps(dict(status='PASS',source=spec.BASE,
            revision='cmp99-physical-prefix-promoted-cold-v1',cold_seal=True)).encode()
        records, axioms = [], {}
        for stage,cmd in spec.commands(prior).items():
            raw = 'SYNTHETIC_NOT_LEAN'
            if stage == 'retained_head': raw = spec.BASE
            if stage == 'mathlib_pin': raw = MATHLIB
            if stage in spec.AXIOMS:
                raw = '\n'.join("'"+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]"
                    for n in sorted(spec.AXIOMS[stage]))
                axioms[stage] = gate.exact_axioms(raw,spec.AXIOMS[stage])
            files[stage+'.log'] = raw.encode()
            records.append(dict(stage=stage,command=cmd,cwd=str(spec.ROOT),exit=0,
                seconds=.01,log=stage+'.log',sha256=sha(raw.encode())))
        outputs = {n:sha(b'SYNTHETIC_OUTPUT') for n in spec.OUTPUTS.values()}
        files.update({n:b'SYNTHETIC_OUTPUT' for n in outputs})
        data = dict(status='PASS',cold_seal=False,source=spec.SOURCE,retained_source=spec.BASE,
            revision=spec.REV,prior_archive_sha256=prior,source_blobs=spec.BLOBS,
            helper_hashes=spec.HELPER_HASHES,records=records,successful_outputs=outputs,
            present_outputs=outputs,axioms=axioms,error=None)
        def pack(fs,d):
            fs['records.json'] = json.dumps(d['records']).encode()
            d['files'] = {n:sha(b) for n,b in fs.items() if n != 'evidence.json'}
            fs['evidence.json'] = json.dumps(d).encode()
            return fs
        pack(files,data)
        verify(files,spec,gate,prior)
        rejected = 0
        for kind in ('head','exit','command','output','missing','sorryAx','ofReduceBool','Other.axiom'):
            fs,d = copy.deepcopy(files),copy.deepcopy(data)
            if kind == 'head':
                fs['retained_head.log'] = b'WRONG_SHA'
                d['records'][1]['sha256'] = sha(fs['retained_head.log'])
            elif kind == 'exit': d['records'][-1]['exit'] = 7
            elif kind == 'command': d['records'][-1]['command'] = ['true']
            elif kind == 'output': fs[next(iter(outputs))] = b'WRONG_OUTPUT'
            elif kind == 'missing': d['axioms'].pop('value_action')
            else:
                name = 'value_action.log'
                fs[name] = fs[name].replace(b'propext',kind.encode(),1)
                next(r for r in d['records'] if r['stage']=='value_action')['sha256'] = sha(fs[name])
            pack(fs,d)
            try: verify(fs,spec,gate,prior)
            except ValueError: rejected += 1
            else: raise AssertionError('CORRUPTION_ACCEPTED='+kind)
        fs,d = copy.deepcopy(files),copy.deepcopy(data)
        d.update(status='FAIL',error='FIRST_ERROR=value_action_repro',records=d['records'][:7],
                 successful_outputs={},present_outputs={},axioms={})
        d['records'][-1]['exit'] = 1
        keep = {'paths.txt','prior-launch-status.json'} | set(source)
        keep |= {r['log'] for r in d['records']}
        fs = {k:v for k,v in fs.items() if k in keep}
        verify(pack(fs,d),spec,gate,prior)
        print('PHYSICAL_VALUE_ACTION_VERIFIER_SELF_TEST=PASS synthetic=1 rejected='+str(rejected)+' fail_prefix=1')
    finally:
        spec.BLOBS = original


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--runner',type=Path,required=True)
    p.add_argument('--axiom-gate',type=Path,required=True)
    p.add_argument('--self-test',action='store_true')
    p.add_argument('--archive',type=Path); p.add_argument('--sha256'); p.add_argument('--prior-sha256')
    args = p.parse_args()
    spec = load(args.runner,RUNNER_HASH)
    for attr in ('ROOT','PRIOR','HELPERS','LOGS'):
        setattr(spec,attr,PurePosixPath(str(getattr(spec,attr)).replace(chr(92),'/')))
    gate = load(args.axiom_gate,GATE_HASH)
    if args.self_test:
        self_test(spec,gate)
        return
    require(args.archive and args.sha256 and args.prior_sha256,'ARCHIVE_ARGUMENTS')
    result = verify(read_archive(args.archive,args.sha256,spec.LOGS.name),
                    spec,gate,args.prior_sha256.lower())
    print(json.dumps(result,sort_keys=True,indent=2))
    print('PHYSICAL_VALUE_ACTION_HOT_PACKAGE_VERIFIED COLD_SEAL=0')


if __name__ == '__main__':
    main()
