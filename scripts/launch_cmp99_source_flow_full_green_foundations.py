"""Single-use pinned Colab launcher: self-test before the fresh source queue."""
import hashlib
from pathlib import Path
import sys
import time
import types
import urllib.request

RAW = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
SOURCE = '098cf3dfad1095c57bdc1d1dc5bc6b13252174d5'
INSTRUMENT = '3dd028d371761e0080fe9573bf750c055fdaae7a'
HELPERS = Path('/content/source-flow-foundations-preflight')


def fetch(commit, path, expected):
    url = RAW + commit + '/' + path
    with urllib.request.urlopen(url, timeout=60) as response:
        blob = response.read()
    digest = hashlib.sha256(blob).hexdigest()
    print('LAUNCHER_TRANSPORT=' + path + ' SHA256=' + digest, flush=True)
    if digest != expected:
        raise RuntimeError('LAUNCHER_HASH_MISMATCH=' + path)
    return blob, url


def main():
    if HELPERS.exists():
        raise RuntimeError('LAUNCHER_ALREADY_STARTED_DO_NOT_REEXECUTE')
    HELPERS.mkdir()
    for name, digest in {
        'verify_cmp99_full_green_residue_cold.py':
            '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c',
        'full_green_owner_exact_axiom_gate.py':
            '016ca4daf0cd06c8016ece106334cc10a4c332c0a58f7f383f03c6f6b3e287c2',
    }.items():
        blob, _ = fetch(SOURCE, 'scripts/' + name, digest)
        (HELPERS / name).write_bytes(blob)
    blob, url = fetch(INSTRUMENT,
        'scripts/verify_cmp99_source_flow_full_green_foundations.py',
        'ee0270aae66bd98a19e22fe4294f44b35afd8d7cfe26f2f3367d51398728506c')
    verifier = types.ModuleType('source_flow_foundations_verifier')
    exec(compile(blob, url, 'exec'), verifier.__dict__)
    sys.argv = [url, '--helpers', str(HELPERS), '--self-test']
    start = time.perf_counter()
    verifier.main()
    print('VERIFIER_SELF_TEST_SECONDS=' + str(time.perf_counter() - start), flush=True)
    print('VERIFIER_SELF_TEST_EXIT=0', flush=True)
    blob, url = fetch(INSTRUMENT,
        'scripts/colab_cmp99_source_flow_full_green_foundations.py',
        'e4dbb6e9205c241a0388f9df7656c39149a2e143c03fa5ac94734819fb1a9d81')
    queue = types.ModuleType('source_flow_foundations_queue')
    exec(compile(blob, url, 'exec'), queue.__dict__)
    return queue.main()


if __name__ == '__main__':
    raise SystemExit(main())
