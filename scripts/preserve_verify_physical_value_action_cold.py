"""Bounded local evidence I/O; no Lean, subprocess, network or worker pool."""
from pathlib import Path
import argparse
import json
import shutil
import time
from preserve_verify_physical_cold_hot_bundle import unpack_tar, load, require, sha

OUTER = 'a9d45101d602321fb86d7268815ebd4bade2ed6a51b2432bcaeb664b1fbd1614'
INNER = '0c4000e3bf98def88f6f96aeaea5d15970d72a43e86458976a68ce2ea7e1f901'
SOURCE = '10437a1a824bdd920282778cabe2f3da6c40ce4e'
REV = 'cmp99-physical-value-action-promoted-cold-v1'

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--archive', type=Path, required=True)
    p.add_argument('--destination', type=Path, required=True)
    args = p.parse_args()
    started = time.perf_counter()
    require(args.archive.stat().st_size == 152264, 'OUTER_SIZE')
    require(sha(args.archive.read_bytes()) == OUTER, 'OUTER_HASH')
    require(not args.destination.exists(), 'DESTINATION_EXISTS_NO_OVERWRITE')
    root = args.destination
    root.mkdir(parents=True)
    shutil.copyfile(args.archive, root / args.archive.name)
    unpack_tar(args.archive, root)
    helpers = root / 'physical-value-action-promoted-cold-v1-launch'
    final = json.loads((helpers / 'launch-final-status.json').read_bytes())
    require(final == dict(status='PASS', source=SOURCE, revision=REV, cold_seal=True),
            'LAUNCH_STATUS')
    records = json.loads((helpers / 'launch-records.json').read_bytes())
    require([r['stage'] for r in records] ==
            ['verifier_self_test', 'physical_cold_graph', 'archive_verifier'], 'LAUNCH_STAGES')
    for record in records:
        require(record['exit'] == 0, 'LAUNCH_EXIT')
        log = helpers / (record['stage'] + '.log')
        require(sha(log.read_bytes()) == record['log_sha256'], 'LAUNCH_LOG_HASH')
    cold = load(helpers / 'verify_cmp99_physical_value_action_promoted_cold.py',
                '9216a5839258e2b2b0a3ec887506ec3ca053d8e858a5a1c46964afbad2f273ae')
    old = cold.helper(helpers, 'verify_cmp99_full_green_residue_cold.py',
                      '558295bb43e74bdae3eb6508656e7b8cde756cb393376320d0c197347396a02c')
    gate = cold.helper(helpers, 'full_green_owner_exact_axiom_gate.py', cold.GATE_HASH)
    old.PREFIX = 'hrpoly-' + REV + '-evidence'
    report = cold.verify(old.read_archive(root / (old.PREFIX + '.tar.gz'), INNER), gate, old)
    require(report['status'] == 'PASS', 'COLD_NOT_PASS')
    result = dict(status='PASS', source=SOURCE, outer_sha256=OUTER,
                  inner_sha256=INNER, launch=records, cold=report,
                  seconds=time.perf_counter()-started,
                  scope='three-name full ambient value action only; no regional B0 or window15')
    output = root / 'independent-local-verification.json'
    output.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n', encoding='utf-8')
    print('PHYSICAL_VALUE_ACTION_COLD_LOCAL_VERIFICATION=PASS')
    print('REPORT_SHA256=' + sha(output.read_bytes()))
    print(json.dumps(result, sort_keys=True))

if __name__ == '__main__':
    main()
