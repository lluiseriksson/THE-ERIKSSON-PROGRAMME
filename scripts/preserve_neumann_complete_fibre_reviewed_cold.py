"""Preserve corrected review without modifying the original FAIL or rerunning Lean."""
import argparse
import json
from pathlib import Path
import sys
import types
from verify_neumann_counting_reflection_diagnostic_v2 import unpack, sha, require

SOURCE = '7f7455b286da5809a0ee64a1511684f887cf8a88'
REV = 'neumann-complete-fibre-promoted-cold-v1'
READER_HASH = '43bd4a309a8696134b1dfc48bcc7014dc0a023f93c1400a3eb90cb02d3c87c22'
FAILURE_READER_HASH = '846f796687279e00162e00a5c4deb4bb9b9e16e06415f5a50b2b26409d0ca118'
def module(path, digest):
    blob = path.read_bytes()
    # Local Git worktrees may use CRLF; executable reference is the LF Git blob.
    blob = blob.replace(b'\r\n', b'\n')
    require(sha(blob) == digest, 'PINNED_READER=' + path.name)
    out = types.ModuleType(path.name)
    exec(compile(blob, path.name, 'exec'), out.__dict__)
    return out, blob
def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--outer-sha256', required=True)
    p.add_argument('--destination', type=Path, required=True)
    a = p.parse_args()
    require(not a.destination.exists(), 'NO_OVERWRITE')
    folder = Path(__file__).resolve().parent
    original, _ = module(folder / 'preserve_neumann_complete_fibre_original_verifier_failure.py', FAILURE_READER_HASH)
    oldargv = sys.argv
    try:
        sys.argv = ['original', '--archive', str(a.archive), '--outer-sha256', a.outer_sha256]
        original.main()
    finally:
        sys.argv = oldargv
    blob = a.archive.read_bytes()
    outer = unpack(blob)
    inner_name = 'hrpoly-' + REV + '-evidence.tar.gz'
    prefix = REV + '-launch/'
    nested = unpack(outer[inner_name])
    ip = 'hrpoly-' + REV + '-evidence/'
    files = {n[len(ip):]: b for n,b in nested.items()}
    reader, reader_blob = module(folder / 'verify_neumann_complete_fibre_promoted_cold_v2.py', READER_HASH)
    old = original.load(outer[prefix + 'verify_cmp99_full_green_residue_cold.py'], 'verify_cmp99_full_green_residue_cold.py')
    gate = original.load(outer[prefix + 'full_green_owner_exact_axiom_gate.py'], 'full_green_owner_exact_axiom_gate.py')
    result = dict(status='PASS_AFTER_READER_CORRECTION', source=SOURCE, cold_seal=True,
        original_launch_status='FAIL', original_error='OWNER_CONTRACT=physical_diagnostic_source',
        original_outer_sha256=sha(blob), inner_sha256=sha(outer[inner_name]),
        corrected_reader_sha256=READER_HASH, no_compiler_reexecution=True,
        cold=reader.verify(files, gate, old), scope=original.SCOPE)
    payload = (json.dumps(result,sort_keys=True,indent=2)+'\n').encode()
    a.destination.mkdir(parents=True,exist_ok=False)
    (a.destination/a.archive.name).write_bytes(blob)
    (a.destination/inner_name).write_bytes(outer[inner_name])
    (a.destination/'corrected-reader.py').write_bytes(reader_blob)
    (a.destination/'reviewed-cold-evidence.json').write_bytes(payload)
    print('REVIEWED_COLD_EVIDENCE=PASS ORIGINAL_FAIL_PRESERVED=1 NO_LEAN_RERUN=1')
    print('REVIEWED_REPORT_SHA256='+sha(payload))
    print(payload.decode())
if __name__ == '__main__':
    main()
