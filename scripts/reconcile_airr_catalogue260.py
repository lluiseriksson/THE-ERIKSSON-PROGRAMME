"""Reconcile one verified public predecessor; never issue grants or receipts.

Default: read-only preview. --apply OLD_RAW_SHA permits only an absent entry.
Run on the existing AIRR host; no credential is read or transmitted.
"""
import hashlib
import json
import os
from pathlib import Path
import sqlite3
import stat
import sys
import urllib.request

PID = 'ARR-2026-597T88D7WZ98HR0Z'
EXPECTED = 'd45a17a4142204628189441b9133aa1027b0d7577a56dc5de6c576d2af6102e7'
CATALOGUE = Path('/srv/airr-private/historical-revisions/catalogue.json')
BACKUP = Path('/srv/airr-private/tep-catalogue-before260C.json')


def get(url, limit):
    request = urllib.request.Request(url, headers={'Cache-Control': 'no-cache'})
    with urllib.request.urlopen(request, timeout=40) as response:
        raw = response.read(limit + 1)
        if response.status != 200 or len(raw) > limit:
            raise RuntimeError('Public HTTP response or size mismatch')
        return raw


def main():
    raw = CATALOGUE.read_bytes()
    data = json.loads(raw)
    release = 'https://github.com/arr-research/arr-research.github.io/releases/download/'
    record = json.loads(get(release + PID + '-v1/RECORD.json', 50000))
    url = 'https://airr.science/papers/' + PID + '/versions/v1/' + PID + '-v1.pdf'
    pdf = get(url, 500000)
    digest = hashlib.sha256(pdf).hexdigest()
    if record['id'] != PID or record['version'] != 'v1':
        raise RuntimeError('Public paper or version mismatch')
    if digest != EXPECTED or len(pdf) != 355193:
        raise RuntimeError('Public PDF mismatch')
    if record['authors'] != [{'name': 'Lluis Eriksson', 'affiliation': 'Independent researcher'}]:
        raise RuntimeError('Public sole-author mismatch')
    if record['integrity']['canonical_sha256'] != digest:
        raise RuntimeError('Public record integrity mismatch')
    entry = {'record_id': record['record_id'], 'version_id': record['version_id'],
             'version': 'v1', 'canonical_sha256': digest, 'authors': ['Lluis Eriksson']}
    if entry['record_id'] != 'arr:record:a93e9086-9f9f-4a23-807e-4551f486306f':
        raise RuntimeError('Public record identity mismatch')
    if entry['version_id'] != 'arr:version:6c269773-95a8-437d-bf09-5c7bc5490273':
        raise RuntimeError('Public version identity mismatch')
    oldsha = hashlib.sha256(raw).hexdigest()
    print(json.dumps({'catalogue_sha256_raw': oldsha, 'old_entry': data.get(PID),
                      'verified_public_entry': entry, 'public_bytes': len(pdf)}), flush=True)
    if len(sys.argv) == 1:
        return
    if sys.argv[1:] != ['--apply', oldsha]:
        raise RuntimeError('Apply arguments do not match observed catalogue bytes')
    if PID in data:
        raise RuntimeError('Existing entry must not be overwritten')
    db = sqlite3.connect('/srv/airr-private/instance/intake.sqlite3', timeout=15)
    try:
        db.execute('BEGIN IMMEDIATE')
        query = ("select count(*) from historical_revision_grants h join agent_grants g "
                 "on h.grant_id=g.id where g.state='approved' and g.uses=0 "
                 "and julianday(g.expires_at)>julianday('now')")
        active_unused = db.execute(query).fetchone()[0]
        if active_unused:
            raise RuntimeError('Live unused historical grants: stop without changing catalogue')
        if CATALOGUE.read_bytes() != raw:
            raise RuntimeError('Concurrent catalogue change')
        with BACKUP.open('xb') as stream:
            stream.write(raw)
            stream.flush()
            os.fsync(stream.fileno())
        prior = dict(data)
        data[PID] = entry
        if any(data[key] != value for key, value in prior.items()):
            raise RuntimeError('Unrelated entry changed')
        new = (json.dumps(data, sort_keys=True, indent=2) + '\n').encode()
        temporary = CATALOGUE.with_name(CATALOGUE.name + '.260C.tmp')
        metadata = CATALOGUE.stat()
        with temporary.open('xb') as stream:
            stream.write(new)
            stream.flush()
            os.fsync(stream.fileno())
        os.chmod(temporary, stat.S_IMODE(metadata.st_mode))
        os.chown(temporary, metadata.st_uid, metadata.st_gid)
        os.replace(temporary, CATALOGUE)
        directory_fd = os.open(CATALOGUE.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
        if CATALOGUE.read_bytes() != new:
            raise RuntimeError('Catalogue readback mismatch')
        db.commit()
        print(json.dumps({'status': 'RECONCILED_VERIFIED_PUBLIC_V1',
                          'active_unused_grants': active_unused,
                          'unrelated_entries_preserved': len(prior),
                          'old_sha256_raw': oldsha,
                          'new_sha256_raw': hashlib.sha256(new).hexdigest()}))
    finally:
        db.close()


if __name__ == '__main__':
    main()
