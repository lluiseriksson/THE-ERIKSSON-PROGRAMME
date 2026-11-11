# SPDX-License-Identifier: AGPL-3.0-or-later
"""Prepare private machine mapping of the actual retained programme instruction.

Read-only SQLite access; never issues scope/grants/cases/permissions. The native
extend-programme-papers command must separately validate and record this evidence.
No owner response, timestamp, licence or original instruction is rewritten.
"""
import hashlib
import json
import os
from pathlib import Path
import sqlite3

PROGRAMME = 'PRG-376B2C03C74C234C0C3F2A42'
INITIAL = '8458953bee142a8d99a6839fef11d1fb004e79681a7ef7df72063ef4479a2d07'
PAPER = 'ARR-2026-597T88D7WZ98HR0Z'
SUFFIX = (' Machine mapping260 of the actual originally authorized sole-author '
          'programme to the existing checkerboard255B record omitted from its machine list; '
          'no new human reply, date, terms, licence, quota, grant or acceptance.')


def derive(initial):
    if (initial.get('programme') != 'THE ERIKSSON PROGRAMME'
            or initial.get('author') != 'Lluis Eriksson'
            or initial.get('rights_confirmed') is not True
            or initial.get('operator_authorship_confirmed') is not True):
        raise ValueError('Unexpected original programme authority')
    evidence = {key: initial[key] for key in
                ('author_instruction', 'recorded_at', 'rights_confirmed',
                 'operator_authorship_confirmed')}
    evidence.update(programme_id=PROGRAMME, initial_instruction_sha256=INITIAL,
                    paper_ids=[PAPER],
                    source_reference=initial['source_reference'] + SUFFIX)
    return (json.dumps(evidence, ensure_ascii=False, indent=2) + '\n').encode()


def main():
    if os.name != 'posix':
        raise ValueError('Existing authenticated AIRR Linux host only')
    uri = 'file:/srv/airr-private/instance/intake.sqlite3?mode=ro'
    with sqlite3.connect(uri, uri=True) as db:
        row = db.execute('SELECT evidence_json,evidence_sha256 FROM '
                         'programme_delegations WHERE id=?', (PROGRAMME,)).fetchone()
        case = db.execute('SELECT s.sha256,s.public_release_url,p.programme_id FROM submissions s '
                          'JOIN agent_submissions m ON m.submission_id=s.id '
                          'JOIN programme_artifact_grants p ON p.grant_id=m.grant_id '
                          'WHERE s.id=?',('SUB-29239472E19C36AB',)).fetchone()
    if row is None or row[1] != INITIAL or hashlib.sha256(row[0].encode()).hexdigest() != INITIAL:
        raise ValueError('Original authority hash mismatch')
    release='https://github.com/arr-research/arr-research.github.io/releases/tag/'+PAPER+'-v1'
    if not case or case != ('d45a17a4142204628189441b9133aa1027b0d7577a56dc5de6c576d2af6102e7',release,PROGRAMME):
        raise ValueError('Verified public predecessor must belong to this actual native programme deposit')
    catalogue = json.loads(Path('/srv/airr-private/historical-revisions/catalogue.json').read_bytes())
    expected = {'record_id': 'arr:record:a93e9086-9f9f-4a23-807e-4551f486306f',
                'version_id': 'arr:version:6c269773-95a8-437d-bf09-5c7bc5490273',
                'version': 'v1',
                'canonical_sha256': 'd45a17a4142204628189441b9133aa1027b0d7577a56dc5de6c576d2af6102e7',
                'authors': ['Lluis Eriksson']}
    if catalogue.get(PAPER) != expected:
        raise ValueError('Verify the actual existing sole-author checkerboard v1 catalogue binding')
    raw = derive(json.loads(row[0]))
    path = Path('/srv/airr-private/tep-scope260-derived.json')
    if path.exists():
        if path.read_bytes() != raw:
            raise ValueError('Preserve differing existing evidence; do not overwrite')
    else:
        fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
        with os.fdopen(fd,'wb') as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
    print(json.dumps({'path': str(path), 'sha256': hashlib.sha256(raw).hexdigest(),
                      'original_instruction_sha256': INITIAL,
                      'original_instruction_unchanged': True,
                      'new_human_response': False, 'scope_recorded': False,
                      'grant_created': False, 'published': False}))


if __name__ == '__main__':
    main()
