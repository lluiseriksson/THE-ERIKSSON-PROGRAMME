"""Bounded evidence I/O only: exact ZIP, safe extraction, pinned verifiers.

No Lean, Lake, network, subprocess or worker pool. Run under a 30s/512MiB
external guard on Windows. A PASS here preserves evidence; it does not
change Lean sources or automatically perform a selective seal.
"""
from pathlib import Path, PurePosixPath
import argparse
import contextlib
import hashlib
import io
import json
import shutil
import tarfile
import time
import types
import zipfile

ZIP_HASH = '69f0b70a76fe636c1e9745c2b3307ad55ddaab99dce838616037e370217e573d'
OUTERS = {
 'physical-prefix-promoted-cold-v1-preservation-20260905.tar.gz': '6075b75a4f58efe929f9f97de12347a700581d8f58034d2b37a96a78b6553a1e',
 'physical-value-action-hot-v1-preservation-20260905.tar.gz': 'dc411e6f16272fd8af308b7f6372d9a5d8ca3128d076f4015e0965f24e05fb75',
}
COLD_INNER = 'd09d7ea9f43027ea203a674a56a4fe4326ad1741cbef00020d38141dfcda9601'
HOT_INNER = '1f5f0f549a9a6f46f82096221b37f81e4c3f68591abaf469598d3fecd89609a9'

def require(ok, message):
    if not ok: raise ValueError(message)

def sha(blob): return hashlib.sha256(blob).hexdigest()

def load(path, digest):
    blob = path.read_bytes()
    require(sha(blob) == digest, 'VERIFIER_HASH=' + path.name)
    mod = types.ModuleType(path.stem)
    mod.__file__ = str(path)
    exec(compile(blob, str(path), 'exec'), mod.__dict__)
    return mod

def unpack_tar(path, target):
    seen, total = set(), 0
    with tarfile.open(path, 'r:gz') as archive:
        for member in archive:
            name = PurePosixPath(member.name)
            require(not name.is_absolute() and '..' not in name.parts
                    and '\\' not in member.name and ':' not in member.name,
                    'UNSAFE_MEMBER')
            require(member.name not in seen and len(seen) < 100, 'DUPLICATE_OR_COUNT')
            seen.add(member.name)
            require(member.isdir() or member.isfile(), 'LINK_OR_SPECIAL_MEMBER')
            require(0 <= member.size <= 4_000_000, 'MEMBER_SIZE')
            total += member.size
            require(total <= 16_000_000, 'EXPANSION_LIMIT')
            out = target.joinpath(*name.parts)
            if member.isdir(): out.mkdir(parents=True, exist_ok=True)
            else:
                out.parent.mkdir(parents=True, exist_ok=True)
                with out.open('xb') as stream:
                    stream.write(archive.extractfile(member).read())

def main():
    started = time.perf_counter()
    p = argparse.ArgumentParser()
    p.add_argument('--zip', type=Path, required=True)
    p.add_argument('--destination', type=Path, required=True)
    args = p.parse_args()
    require(args.zip.stat().st_size == 364510, 'ZIP_SIZE')
    require(sha(args.zip.read_bytes()) == ZIP_HASH, 'ZIP_HASH')
    require(not args.destination.exists(), 'DESTINATION_EXISTS_NO_OVERWRITE')
    with zipfile.ZipFile(args.zip) as archive:
        members = archive.infolist()
        require(len(members) == 2 and {m.filename for m in members} == set(OUTERS), 'ZIP_MEMBERS')
        blobs = {}
        for member in members:
            require(0 < member.file_size < 400000, 'ZIP_MEMBER_SIZE')
            blob = archive.read(member)
            require(sha(blob) == OUTERS[member.filename], 'OUTER_HASH')
            blobs[member.filename] = blob
    root = args.destination
    root.mkdir(parents=True)
    shutil.copyfile(args.zip, root / args.zip.name)
    for name, blob in blobs.items():
        path = root / name
        path.write_bytes(blob)
        unpack_tar(path, root)
    cw = root / 'physical-prefix-promoted-cold-v1-launch'
    hw = root / 'physical-value-action-hot-v1-launch'
    cold = load(cw / 'verify_cmp99_physical_prefix_promoted_cold.py',
                '0736f672ff3aa13464a8cd167d834d93db6175ece21abc1c48bfc8807bf869cc')
    old = cold.helper(cw, 'verify_cmp99_full_green_residue_cold.py',
                      '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')
    gate = cold.helper(cw, 'full_green_owner_exact_axiom_gate.py', cold.GATE_HASH)
    old.PREFIX = 'hrpoly-' + cold.REV + '-evidence'
    cold_report = cold.verify(old.read_archive(root / (old.PREFIX + '.tar.gz'), COLD_INNER), gate, old)
    require(cold_report['status'] == 'PASS', 'COLD_NOT_PASS')
    hot = load(hw / 'verify_cmp99_physical_value_action_hot.py',
               'ee9216ee2b519aa76ab04d075b31244f401cb93a679d1336e38ea93fa2d2c14f')
    spec = hot.load(hw / 'colab_cmp99_physical_value_action_hot.py', hot.RUNNER_HASH)
    for attr in ('ROOT', 'PRIOR', 'HELPERS', 'LOGS'):
        setattr(spec, attr, PurePosixPath(str(getattr(spec, attr)).replace(chr(92), '/')))
    hot_gate = hot.load(hw / 'full_green_owner_exact_axiom_gate.py', hot.GATE_HASH)
    hot_report = hot.verify(hot.read_archive(root / 'cmp99-physical-value-action-hot-v1-logs.tar.gz',
                           HOT_INNER, spec.LOGS.name), spec, hot_gate, COLD_INNER)
    require(hot_report['status'] == 'PASS', 'HOT_NOT_PASS')
    report = dict(status='PASS', zip_sha256=ZIP_HASH, outer_sha256=OUTERS,
                  cold_inner_sha256=COLD_INNER, hot_inner_sha256=HOT_INNER,
                  cold=cold_report, hot=hot_report,
                  seconds=time.perf_counter()-started,
                  scope='independent local evidence verification; HOT is not cold seal')
    output = root / 'independent-local-verification.json'
    output.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n', encoding='utf-8')
    print('PHYSICAL_COLD_AND_HOT_LOCAL_VERIFICATION=PASS')
    print('REPORT_SHA256=' + sha(output.read_bytes()))
    print('SECONDS=' + str(report['seconds']))
    print(json.dumps(report, sort_keys=True))

if __name__ == '__main__': main()
