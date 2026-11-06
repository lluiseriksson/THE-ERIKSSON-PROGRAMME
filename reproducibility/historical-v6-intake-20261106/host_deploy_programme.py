"""Install reviewed AIRR programme code without issuing persistent access.

Existing authenticated root host, original encrypted-backup/offsite/upgrade
procedures, unchanged final environment, no new keys, grants or users.
"""
from datetime import datetime, timezone, timedelta
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sqlite3
import subprocess
import sys
import time
import urllib.request

COMMIT = 'f44781be89e8ecb0640983e66f1d5608046c8e96'
PREVIOUS = '06d7c2e09c66ded8772f2e1b92b3f5f88d2b155f'
UPGRADE_SHA = '28ff0ed303d5106a318d8627763e71330fafb41a80f2ef7052bc5dca596e7148'
ROOT = Path('/srv/airr-private/eriksson-autonomy-20261106')
CONFIG = Path('/etc/airr-intake/intake.env')


def save(name, value):
    path = ROOT/name
    path.write_text(json.dumps(value, indent=2)+'\n')
    path.chmod(0o600)


def command(name, *args, timeout=1500):
    with (ROOT/(name+'.log')).open('ab') as log:
        subprocess.run(args, check=True, stdout=log, stderr=subprocess.STDOUT, timeout=timeout)


def main():
    if os.geteuid() != 0 or not os.path.ismount('/srv/airr-private'):
        raise ValueError('Existing authenticated host and mounted encrypted volume required')
    os.umask(0o077)
    ROOT.mkdir(mode=0o700, exist_ok=True)
    if (ROOT/'deployment-result.json').exists():
        print((ROOT/'deployment-result.json').read_text(), flush=True)
        return
    previous = Path('/opt/airr-intake/current').resolve()
    if not re.fullmatch(r'[0-9a-f]{40}', PREVIOUS):
        raise ValueError('Pinned previous source must be a complete 40-hex SHA')
    if previous.name != PREVIOUS or (ROOT/'intake-before.env').exists():
        raise ValueError('Unexpected release or earlier partial operation; reconcile before retrying')
    started = datetime.now(timezone.utc)
    raw = urllib.request.urlopen('https://raw.githubusercontent.com/arr-research/arr-research.github.io/'+COMMIT+'/services/intake/deploy/upgrade.py', timeout=45).read()
    if hashlib.sha256(raw).hexdigest() != UPGRADE_SHA:
        raise ValueError('Reviewed upgrade helper hash mismatch')
    upgrade = ROOT/'upgrade.py'
    upgrade.write_bytes(raw)
    original = CONFIG.read_bytes()
    text = original.decode()
    if len(re.findall(r'^ARR_INTAKE_OPEN=.*$', text, re.M)) != 1:
        raise ValueError('Explicit existing intake configuration required')
    shutil.copy2(CONFIG, ROOT/'intake-before.env')
    save('phase.json', {'phase': 'prepared', 'started_at': started.isoformat(), 'previous_release': previous.name, 'new_release': COMMIT})
    try:
        CONFIG.write_text(re.sub(r'^ARR_INTAKE_OPEN=.*$', 'ARR_INTAKE_OPEN=0', text, flags=re.M))
        command('pause-intake', 'systemctl', 'restart', 'airr-intake.service', timeout=90)
        save('phase.json', {'phase': 'intake_paused', 'started_at': started.isoformat()})
        command('backup-before', 'systemctl', 'start', 'airr-intake-backup.service')
        command('offsite-before', 'systemctl', 'start', 'airr-intake-offsite.service')
        offsite = json.loads(Path('/var/lib/airr-offsite/status.json').read_bytes())
        verified = datetime.fromisoformat(offsite['verified_at'])
        snapshot = datetime.fromisoformat(offsite['snapshot_at'])
        if not offsite.get('ok') or not offsite.get('download_verified') or verified < started or snapshot < started-timedelta(seconds=60):
            raise ValueError('Fresh encrypted snapshot and independent download verification required')
        save('offsite-before.json', offsite)
        save('phase.json', {'phase': 'verified_backup_ready', 'started_at': started.isoformat()})
        command('upgrade', sys.executable, str(upgrade), COMMIT, timeout=900)
    finally:
        # Restore exact original config and its permissions; never print it.
        CONFIG.write_bytes(original)
        shutil.copystat(ROOT/'intake-before.env', CONFIG)
        command('restore-intake', 'systemctl', 'restart', 'airr-intake.service', timeout=90)
    if Path('/opt/airr-intake/current').resolve().name != COMMIT:
        raise ValueError('Expected reviewed source is not active')
    ready = False
    for _ in range(30):
        try:
            with urllib.request.urlopen('http://127.0.0.1:8000/readyz', timeout=5) as response:
                ready = response.status == 200
            if ready:
                break
        except OSError:
            pass
        time.sleep(1)
    if not ready:
        raise ValueError('Readiness did not pass after restart')
    with sqlite3.connect('/srv/airr-private/instance/intake.sqlite3') as db:
        if db.execute('PRAGMA integrity_check').fetchone()[0] != 'ok':
            raise ValueError('Database integrity failed')
        programme_count = db.execute('SELECT COUNT(*) FROM programme_delegations').fetchone()[0]
    after_started = datetime.now(timezone.utc)
    command('backup-after', 'systemctl', 'start', 'airr-intake-backup.service')
    command('offsite-after', 'systemctl', 'start', 'airr-intake-offsite.service')
    after = json.loads(Path('/var/lib/airr-offsite/status.json').read_bytes())
    if (not after.get('ok') or not after.get('download_verified')
            or datetime.fromisoformat(after['verified_at']) < after_started
            or datetime.fromisoformat(after['snapshot_at']) < after_started-timedelta(seconds=60)):
        raise ValueError('Post-deployment encrypted offsite verification failed')
    save('offsite-after.json', after)
    proof = json.loads((Path('/srv/airr-private')/('rollback-'+COMMIT[:12])/'deployment.json').read_bytes())
    proof.update(started_at=started.isoformat(), finished_at=datetime.now(timezone.utc).isoformat(),
                 original_environment_restored=True, programme_grants_present=programme_count,
                 new_programme_controller_issued=False, activation_not_performed=True,
                 before_offsite_download_verified=True, after_offsite_download_verified=True)
    save('deployment-result.json', proof)
    print(json.dumps(proof), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if ROOT.exists():
            save('deployment-error.json', {'error_type': type(error).__name__, 'message': str(error)})
        raise
