"""Bounded local evidence I/O; no Lean, subprocess, network or worker pool."""
from pathlib import Path
import argparse
import json
import shutil
from preserve_verify_physical_cold_hot_bundle import unpack_tar, load, require, sha

SOURCE = '59160603dda023d9f577ea7edc96f24995de1ac5'
REV = 'neumann-halfcell-block-reflection-cold-v1'
VERIFIER = 'bf28ff31a459dd761dceca1a5d91f96d7c51d62c07f6f1aaf40c5abf38258159'

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--outer-sha256', required=True)
    p.add_argument('--inner-sha256', required=True)
    p.add_argument('--destination', type=Path, required=True)
    a = p.parse_args()
    require(a.archive.stat().st_size < 8_000_000, 'OUTER_SIZE')
    require(sha(a.archive.read_bytes()) == a.outer_sha256.lower(), 'OUTER_HASH')
    require(not a.destination.exists(), 'DESTINATION_EXISTS_NO_OVERWRITE')
    root = a.destination
    root.mkdir(parents=True)
    shutil.copyfile(a.archive, root / a.archive.name)
    unpack_tar(a.archive, root)
    helpers = root / (REV + '-launch')
    final = json.loads((helpers / 'launch-final-status.json').read_bytes())
    require(final == dict(status='PASS', source=SOURCE, revision=REV, cold_seal=True),
            'LAUNCH_STATUS')
    records = json.loads((helpers / 'launch-records.json').read_bytes())
    require([r['stage'] for r in records] ==
            ['verifier_self_test', 'physical_cold_graph', 'archive_verifier'], 'LAUNCH_STAGES')
    for r in records:
        require(r['exit'] == 0, 'LAUNCH_EXIT')
        require(sha((helpers / (r['stage']+'.log')).read_bytes()) == r['log_sha256'],
                'LAUNCH_LOG_HASH')
    cold = load(helpers / 'verify_neumann_halfcell_reflection_cold.py', VERIFIER)
    old = cold.helper(helpers, 'verify_cmp99_full_green_residue_cold.py',
                      '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')
    gate = cold.helper(helpers, 'full_green_owner_exact_axiom_gate.py', cold.GATE_HASH)
    old.PREFIX = 'hrpoly-' + REV + '-evidence'
    report = cold.verify(old.read_archive(root / (old.PREFIX+'.tar.gz'), a.inner_sha256), gate, old)
    result = dict(status='PASS', source=SOURCE, outer_sha256=a.outer_sha256.lower(),
                  inner_sha256=a.inner_sha256.lower(), launch=records, cold=report,
                  scope='half-cell block geometry only; not Q intertwining or regional inverse')
    out = root / 'independent-local-verification.json'
    out.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n', encoding='utf-8')
    print('NEUMANN_HALFCELL_COLD_LOCAL_VERIFICATION=PASS')
    print('REPORT_SHA256=' + sha(out.read_bytes()))
    print(json.dumps(result, sort_keys=True))

if __name__ == '__main__':
    main()
