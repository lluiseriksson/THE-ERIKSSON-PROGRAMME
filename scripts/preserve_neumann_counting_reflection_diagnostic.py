"""Preserve an independently verified diagnostic; no compiler/network/pool.

All archive verification completes before creating the destination. This
does not promote the mathematical source or turn a HOT diagnostic into a
cold seal. Existing destinations are never overwritten.
"""
import argparse
import contextlib
import io
import json
from pathlib import Path
import sys

import verify_neumann_counting_reflection_diagnostic as verifier


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--sha256', required=True)
    parser.add_argument('--axiom-helper', type=Path, required=True)
    parser.add_argument('--destination', type=Path, required=True)
    args = parser.parse_args()
    verifier.require(not args.destination.exists(), 'DESTINATION_EXISTS_NO_OVERWRITE')
    verifier.require(args.archive.stat().st_size <= 64 * 2**20, 'ARCHIVE_SIZE')
    # Use exactly the independent verifier, including its pinned axiom helper.
    saved_argv = sys.argv
    captured = io.StringIO()
    try:
        sys.argv = [str(Path(verifier.__file__)), '--archive', str(args.archive),
            '--sha256', args.sha256, '--axiom-helper', str(args.axiom_helper)]
        with contextlib.redirect_stdout(captured):
            verifier.main()
    finally:
        sys.argv = saved_argv
    blob = args.archive.read_bytes()
    # Recheck bytes used for preservation, not just an earlier file read.
    verifier.require(verifier.sha(blob) == args.sha256.lower(), 'PRESERVATION_HASH')
    outer = verifier.unpack(blob)
    inner_name = 'hrpoly-' + verifier.REV + '-evidence.tar.gz'
    nested = verifier.unpack(outer[inner_name])
    verifier.require(not set(outer).intersection(nested), 'NESTED_PATH_COLLISION')
    files = {**outer, **nested}
    root = args.destination
    root.mkdir(parents=True, exist_ok=False)
    (root / args.archive.name).write_bytes(blob)
    for name, payload in files.items():
        target = root.joinpath(*Path(name).parts)
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as out:
            out.write(payload)
    transcript = captured.getvalue().encode('utf-8')
    (root / 'independent-verification.txt').write_bytes(transcript)
    record = dict(status='PASS', cold_seal=False, source=verifier.SOURCE,
        revision=verifier.REV, outer_sha256=verifier.sha(blob),
        inner_sha256=verifier.sha(outer[inner_name]),
        verification_sha256=verifier.sha(transcript),
        scope='full-carrier counting-mass diagnostic only; not retained Neumann inverse',
        preserved={name: verifier.sha(payload) for name, payload in sorted(files.items())})
    payload = (json.dumps(record, sort_keys=True, indent=2) + '\n').encode('utf-8')
    (root / 'independent-preservation.json').write_bytes(payload)
    print('COUNTING_REFLECTION_DIAGNOSTIC_PRESERVED COLD_SEAL=0')
    print('PRESERVATION_RECORD_SHA256=' + verifier.sha(payload))
    print(captured.getvalue(), end='')


if __name__ == '__main__':
    main()
