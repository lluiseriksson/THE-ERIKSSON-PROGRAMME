"""Host-portability adapter for the immutable Linux retry-v2 verifier.

The old verifier imports a runner whose pathlib.Path constructs expected
Linux command strings as Windows paths on Windows. Normalize ONLY those
expected /content paths; never transform archive data, logs or source bytes.
All original digest, exit, exact axiom and output checks still run unchanged.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import types

VERIFIER_HASH = '072c4a6691f0c58eddc1933390e21677e9f8f6f5ef579b3d49719133c6e20a98'


def main():
    p = argparse.ArgumentParser()
    p.add_argument('--helpers',type=Path,required=True)
    p.add_argument('--archive',type=Path,required=True)
    p.add_argument('--sha256',required=True)
    args = p.parse_args()
    blob = (args.helpers/'verify_cmp99_physical_real_slice_retry.py').read_bytes()
    if hashlib.sha256(blob).hexdigest() != VERIFIER_HASH:
        raise ValueError('VERIFIER_HASH')
    verifier = types.ModuleType('immutable_retry_v2_verifier')
    exec(compile(blob,'pinned_retry_v2_verifier','exec'),verifier.__dict__)
    spec = verifier.load(args.helpers,'colab_cmp99_physical_real_slice_retry.py')
    old = verifier.load(args.helpers,'verify_cmp99_full_green_residue_cold.py')
    gate = verifier.load(args.helpers,'full_green_owner_exact_axiom_gate.py')
    def posix(s):
        return s.replace('\\','/') if s.startswith('\\content\\') else s
    original = {s:list(cmd) for s,cmd in spec.COMMANDS.items()}
    spec.COMMANDS = {s:[posix(a) for a in cmd] for s,cmd in original.items()}
    for attr in ('ROOT','EVIDENCE'):
        setattr(spec,attr,PurePosixPath(posix(str(getattr(spec,attr)))))
    old.PREFIX = spec.EVIDENCE.name
    verifier.self_test(spec,old,gate)
    report = verifier.verify(old.read_archive(args.archive,args.sha256),spec,old,gate)
    print(json.dumps(dict(adapter='expected-linux-paths-only',
        expected_commands_before=original,expected_commands_after=spec.COMMANDS,
        archive_bytes_transformed=False,report=report),sort_keys=True,indent=2))
    print('PHYSICAL_RETRY_V2_POSIX_ADAPTER_VERIFIED COLD_SEAL=0')


if __name__ == '__main__':
    main()
