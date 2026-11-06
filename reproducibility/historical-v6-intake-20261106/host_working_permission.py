"""Record the ACTUAL exact-v6 author instruction using tested AIRR CLI code.

Authenticated host only. No fake browser session, acceptance, new receipt or
grant. The existing actual author approval and native receipt must already exist.
"""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import urllib.request

ROOT = Path('/srv/airr-private/eriksson-v6-20261106')
SHA = 'ccf53e0afc9819c3fc9b2008de9076a60f60d23ef6ac2c4ccd82adca30cbf389'
SOURCE = 'https://raw.githubusercontent.com/arr-research/arr-research.github.io/f44781be89e8ecb0640983e66f1d5608046c8e96/services/intake/external_editorial.py'
CODE_SHA = 'dfdac8ce791ba2379d3929ad76bf191d3c5d32cbb4b5f29733a76ac32a8ef771'


def save(name, value):
    path = ROOT/name
    with path.open('wb') as stream:
        os.fchmod(stream.fileno(), 0o600)
        stream.write(value if isinstance(value, bytes) else json.dumps(value, ensure_ascii=False, indent=2).encode())
    return path


def main():
    if os.getuid() != 0:
        raise ValueError('Existing authenticated host operator required')
    os.umask(0o077)
    approval = json.loads((ROOT/'actual-human-approval.json').read_bytes())
    receipt = json.loads((ROOT/'receipt.json').read_bytes())
    if approval['sha256'] != SHA or receipt['sha256'] != SHA or receipt['scan_status'] != 'clean' or approval['actual_human_answer'] != 'Confirmo y autorizo este PDF y esas condiciones':
        raise ValueError('Actual exact-artifact author instruction and clean native receipt required')
    raw = urllib.request.urlopen(SOURCE, timeout=30).read()
    if hashlib.sha256(raw).hexdigest() != CODE_SHA:
        raise ValueError('Tested application CLI source hash mismatch')
    code = save('tested_external_editorial.py', raw)
    sys.path.insert(0, '/opt/airr-intake/current')
    from services.intake import app as a
    app = a.create_app()
    spec = importlib.util.spec_from_file_location('tep_tested_external_editorial', code)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    def case(identity):
        row = a.get_db().execute('SELECT * FROM submissions WHERE id=?', (identity,)).fetchone()
        if not row:
            raise ValueError('Actual native case absent')
        return row
    module.install(app, a, case)
    evidence = {'submission_id': receipt['registration_number'], 'manuscript_sha256': SHA,
                'human_name': 'Lluis Eriksson',
                'human_instruction': 'Actual author replied to the exact46page PDF question confirming authorship and rights, current terms/privacy, one linked revision, and diffusion as a Working paper under CC BY4.0 with CC0 metadata. Actual answer: '+approval['actual_human_answer'],
                'source_reference': approval['source_reference'], 'recorded_at': approval['recorded_at'],
                'license': 'CC-BY-4.0', 'metadata_license': 'CC0-1.0',
                'rights_confirmed': True, 'founder_authorship_confirmed': True}
    path = save('actual-working-permission-evidence.json', evidence)
    result = app.test_cli_runner().invoke(args=['record-external-working-publication', str(path)])
    if result.exit_code:
        raise ValueError('Native tested Working-paper CLI rejected: '+result.output)
    outcome = json.loads(result.output)
    with app.app_context():
        db = a.get_db()
        permission = db.execute('SELECT * FROM publication_permissions WHERE submission_id=?', (receipt['registration_number'],)).fetchone()
        row = case(receipt['registration_number'])
        outcome['permission'] = dict(permission)
        outcome['founder_declared_at'] = row['founder_declared_at']
        outcome['working_case_status'] = row['status']
    save('actual-working-permission-result.json', outcome)
    print(json.dumps(outcome), flush=True)


if __name__ == '__main__':
    main()
