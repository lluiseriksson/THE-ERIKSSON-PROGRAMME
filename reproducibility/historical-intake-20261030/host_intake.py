"""Exact historical revision through AIRR's existing guarded CLI and HTTPS API.

inspect is read-only apart from private evidence files. deposit issues one native
exact-artifact grant and uploads once with a persistent idempotency key. It does
not create users, change policies, bypass quotas, accept or publish a manuscript.
Run only on the authenticated AIRR host with its existing service environment.
"""
import argparse
from datetime import timedelta
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import urllib.request
import uuid

ROOT = Path('/srv/airr-private/eriksson-historical-20261030')
BASE = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
FOLDER = '/reproducibility/historical-intake-20261030/'
PID = 'ARR-2026-7EPM3V3DP796BBRR'
SHA = 'b37f2fe86b7a8a526ad02f8b28491c300a9ff72d5653536bc5532e8c9468ed8f'
PINS = {'binding.json':'59b7d89c976462e2e491c745b65ee54fe97ed51ece41e915e66e4ff6d596d066',
        'revision-job.json':'270b0cf7890dc4dcba4f99d977207256448af2c523e5954d01b10e2e11448574'}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def save(name, data):
    p = ROOT/name
    raw = data if isinstance(data, bytes) else json.dumps(data, indent=2).encode()
    with open(p, 'wb') as stream:
        os.fchmod(stream.fileno(), 0o600)
        stream.write(raw)
    return p


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise ValueError('Unexpected redirect; no credential redirected.')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('mode', choices=['inspect', 'deposit', 'receipt'])
    parser.add_argument('source_sha')
    args = parser.parse_args()
    if not re.fullmatch('[a-f0-9]{40}', args.source_sha):
        raise ValueError('Pinned source commit required')
    if os.getuid() != 0:
        raise ValueError('Existing authenticated host operator required')
    os.umask(0o077)
    ROOT.mkdir(mode=0o700, exist_ok=True)
    for name, expected in PINS.items():
        raw = urllib.request.urlopen(BASE+args.source_sha+FOLDER+name, timeout=30).read()
        if digest(raw) != expected:
            raise ValueError('Pinned input mismatch')
        save(name, raw)
    binding = json.loads((ROOT/'binding.json').read_bytes())
    job = json.loads((ROOT/'revision-job.json').read_bytes())
    pdf = urllib.request.urlopen(BASE+'a9937ee1dd5978bf372174500a2395cf259eb395/papers/flat-coarse-rank/flat_coarse_rank.pdf', timeout=30).read()
    if digest(pdf) != SHA or binding['sha256'] != SHA or job['metadata']['sha256'] != SHA or binding['paper_id'] != PID:
        raise ValueError('Exact PDF/binding mismatch')
    save('paper.pdf', pdf)
    sys.path.insert(0, '/opt/airr-intake/current')
    from services.intake import app as a
    from services.intake.historical_revisions import catalogue, validate_binding
    app = a.create_app()
    with app.app_context():
        entries, catalogue_hash = catalogue(app)
        db = a.get_db()
        try:
            validate_binding(binding, entries, app.config.get('HISTORICAL_OPERATOR_AUTHOR'))
        except ValueError as error:
            pending=db.execute("SELECT COUNT(*) FROM historical_revision_grants h JOIN agent_grants g ON g.id=h.grant_id WHERE g.state='approved' AND g.expires_at>? AND g.uses=0", (a.iso(),)).fetchone()[0]
            diagnostic={'checked_at':a.iso(),'binding_rejected':str(error),'configured_operator_author':app.config.get('HISTORICAL_OPERATOR_AUTHOR'),'target_catalogue_entry':entries.get(PID),'catalogue_path':app.config['HISTORICAL_REVISION_CATALOGUE'],'catalogue_sha256':catalogue_hash,'unconsumed_unexpired_historical_grants':pending,'grant_issued':False,'uploaded':False}
            save('catalogue-diagnostic.json',diagnostic)
            print(json.dumps(diagnostic),flush=True)
            raise
        owner = db.execute("SELECT u.id,u.active,u.role,p.alias,p.identity_kind,p.terms_version,p.privacy_version FROM users u JOIN private_accounts p ON p.user_id=u.id WHERE p.alias=?", ('lluiseriksson',)).fetchone()
        actor = db.execute("SELECT id FROM users WHERE email=? AND role='operator' AND active=1 AND totp_secret IS NOT NULL", (app.config['OPERATOR_EMAIL'],)).fetchone()
        if not owner or not owner['active'] or owner['role'] != 'depositor' or owner['identity_kind'] != 'human' or not actor:
            raise ValueError('Real active owner and existing MFA operator required')
        if owner['terms_version'] != a.TERMS_VERSION or owner['privacy_version'] != a.PRIVACY_VERSION:
            raise ValueError('Current owner terms/privacy acknowledgment missing; no acknowledgment invented')
        cutoff = a.iso(a.now()-timedelta(hours=24))
        recent = db.execute('SELECT COUNT(*) FROM submissions WHERE user_id=? AND created_at>=?', (owner['id'],cutoff)).fetchone()[0]
        existing = db.execute("SELECT s.id,s.sha256,s.scan_status,s.status FROM historical_revisions h JOIN submissions s ON s.id=h.submission_id WHERE h.version_id=? OR (h.binding_json LIKE ?)", (binding['version_id'],'%'+SHA+'%')).fetchall()
        inspection = {'checked_at':a.iso(), 'paper_id':PID, 'sha256':SHA, 'catalogue_binding_valid':True, 'catalogue_sha256':catalogue_hash, 'owner_id':owner['id'], 'owner_alias':owner['alias'], 'mfa_operator_ready':bool(actor), 'current_acknowledgments_match':True, 'terms_version':a.TERMS_VERSION, 'privacy_version':a.PRIVACY_VERSION, 'owner_deposits_last_24h':recent, 'existing_cases':[dict(x) for x in existing], 'accepted':False, 'published':False}
        save('inspection.json',inspection)
        if args.mode == 'inspect':
            print(json.dumps(inspection),flush=True)
            return
        if args.mode == 'deposit':
            if (ROOT/'receipt.json').exists():
                print((ROOT/'receipt.json').read_text(),flush=True)
                return
            if existing:
                raise ValueError('Matching historical candidate exists; reconcile its case/receipt instead of redepositing')
            if recent >= 10:
                raise ValueError('Rolling quota unavailable; no bypass')
            if not (ROOT/'grant.json').exists():
                evidence = {'owner_user_id':owner['id'], 'agent_name':'THE ERIKSSON PROGRAMME coordinator', 'agent_version':'Codex desktop historical revision027', 'binding':binding, 'author_instruction':'Lluis authorized autonomous consolidation, review and AIRR publication through existing routes in this research chat on29October2026; after preparation of this exact revision and disclosure of the host-access requirement, he completed Netcup sign-in and stated listo on30October2026. This records that instruction, not a web signature or independent decision.', 'source_reference':'Programme chat01a1860c-7a67-7de3-9f5c-b0a994500145; authorization29October2026; exact-artifact packet026 and completed Netcup login30October2026.', 'recorded_at':a.iso(), 'scope':['revision:create','submission:receipt'], 'terms_version':a.TERMS_VERSION, 'privacy_version':a.PRIVACY_VERSION, 'operator_authorship_confirmed':True}
                evidence_path=save('historical-authorization.json',evidence)
                result=app.test_cli_runner().invoke(args=['authorize-historical-revision',str(evidence_path)])
                if result.exit_code:
                    raise ValueError('Native historical authorization rejected: '+result.output)
                save('grant.json',json.loads(result.output))
            grant=json.loads((ROOT/'grant.json').read_bytes())
            boundary='ERIKSSON'+uuid.uuid4().hex
            body=(f'--{boundary}\r\nContent-Disposition: form-data; name="metadata"\r\nContent-Type: application/json\r\n\r\n'.encode()+json.dumps(job['metadata']).encode()+f'\r\n--{boundary}\r\nContent-Disposition: form-data; name="manuscript"; filename="flat-coarse-rank-v2.pdf"\r\nContent-Type: application/pdf\r\n\r\n'.encode()+pdf+f'\r\n--{boundary}--\r\n'.encode())
            req=urllib.request.Request('https://submit.airr.science/api/v1/revisions',data=body,headers={'Authorization':'Bearer '+grant['agent_token'],'Idempotency-Key':job['idempotency_key'],'Content-Type':'multipart/form-data; boundary='+boundary})
        else:
            if not (ROOT/'receipt.json').exists() or not (ROOT/'grant.json').exists():
                raise ValueError('No local receipt/grant to reconcile')
            prior=json.loads((ROOT/'receipt.json').read_bytes())
            grant=json.loads((ROOT/'grant.json').read_bytes())
            req=urllib.request.Request('https://submit.airr.science/api/v1/submissions/'+prior['registration_number'],headers={'Authorization':'Bearer '+grant['agent_token']})
        opener=urllib.request.build_opener(NoRedirect)
        with opener.open(req,timeout=60) as response:
            raw=response.read()
        receipt=json.loads(raw)
        if receipt['sha256'] != SHA or receipt['historical_revision'] != binding:
            raise ValueError('Receipt artifact/binding mismatch')
        save('receipt.json',raw)
        print(json.dumps(receipt),flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(json.dumps({'error_type':type(error).__name__,'error':str(error),'no_automatic_retry_or_renewal':True}),flush=True)
        raise SystemExit(1)
