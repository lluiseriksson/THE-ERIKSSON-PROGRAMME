"""Exact historical revision through AIRR's existing guarded CLI and HTTPS API.

inspect is read-only apart from private evidence files. deposit issues one native
exact-artifact grant and uploads once with a persistent idempotency key. It does
not create users, change policies, bypass quotas, accept or publish a manuscript.
Run only on the authenticated AIRR host with its existing service environment.
"""
import argparse
from datetime import datetime, timedelta
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import urllib.request
import uuid

ROOT = Path('/srv/airr-private/eriksson-v3-20261031')
BASE = 'https://raw.githubusercontent.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/'
FOLDER = '/reproducibility/historical-v3-intake-20261031/'
PID = 'ARR-2026-7EPM3V3DP796BBRR'
SHA = 'c9de923a66038ed66c3f68ecf8256b3f738a3ccf27e41f77e470bf7dc3efb5b9'
PINS = {'binding.json':'ad54b40de9b60b6c5159ff8a171532ac98f148bcefcd2c2e596318774865c93f','revision-job.json':'4cb3d90ce979a81da189ba178a2ab27a1f6d14eed60a3c37f2145eea348c1825'}


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
    parser.add_argument('mode', choices=['inspect', 'approve', 'deposit', 'receipt'])
    parser.add_argument('source_sha')
    parser.add_argument('--approval-file')
    parser.add_argument('--approval-sha256')
    parser.add_argument('--answer-b64')
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
    pdf = urllib.request.urlopen(BASE+'ba71e81cb07cd35578de9aac11d0992ff78061b5/papers/flat-coarse-rank/v3-candidate/flat_coarse_rank.pdf', timeout=30).read()
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
        if args.mode == 'approve':
            import base64
            if not args.answer_b64:
                raise ValueError('Actual exact-artifact human reply required')
            answer = base64.b64decode(args.answer_b64, validate=True).decode('utf-8')
            if len(answer) < 20 or len(answer) > 2000:
                raise ValueError('Preserve the actual human answer')
            prior_path=Path('/srv/airr-private/eriksson-historical-20261030/approval32.json')
            prior=json.loads(prior_path.read_bytes())
            if (prior['terms_version'] != a.TERMS_VERSION or prior['privacy_version'] != a.PRIVACY_VERSION
                or prior['accepted_terms'] is not True or prior['read_privacy'] is not True):
                raise ValueError('Earlier real terms/privacy acknowledgment does not cover current contract')
            approval={'paper_id':PID,'sha256':SHA,'terms_version':a.TERMS_VERSION,
                'privacy_version':a.PRIVACY_VERSION,'accepted_terms':True,'read_privacy':True,
                'approve_exact_grant':True,
                'source_reference':'Actual user reply to call_ee705187dbe048739d3b06b6b68430d5 in programme chat; same current terms/privacy actually acknowledged in prior approval32.json, not a fresh assent invented here',
                'actual_human_answer':answer,'recorded_at':a.iso()}
            raw=json.dumps(approval,ensure_ascii=False,indent=2).encode()
            if (ROOT/'approval-v3.json').exists():
                raise ValueError('Approval already recorded; inspect instead of overwriting')
            save('approval-v3.json',raw)
            save('approval-v3.sha256',digest(raw).encode())
            save('publication-instruction.json',{'paper_id':PID,'sha256':SHA,
                'actual_human_answer':answer,'source_reference':approval['source_reference'],
                'recorded_at':approval['recorded_at'],'only_existing_predecessor_refresh':True,
                'historical_grant_hours':24,'historical_grant_uses':1,
                'publish_as':'Working paper — no admitido','pdf_license':'CC-BY-4.0','metadata_license':'CC0'})
            print(json.dumps({'approval_recorded':True,'sha256':SHA,'approval_sha256':digest(raw),
                'prior_terms_ack_reused_unchanged':True,'grant_issued':False,'uploaded':False}),flush=True)
            return
        if args.mode == 'deposit' and not args.approval_file and not args.approval_sha256:
            args.approval_file=str(ROOT/'approval-v3.json')
            args.approval_sha256=(ROOT/'approval-v3.sha256').read_text().strip()
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
        account_ack_match = (owner['terms_version'] == a.TERMS_VERSION and owner['privacy_version'] == a.PRIVACY_VERSION)
        approval = None
        if args.mode == 'deposit':
            if not args.approval_file or not args.approval_sha256 or not re.fullmatch('[a-f0-9]{64}', args.approval_sha256):
                raise ValueError('Exact recent human terms/privacy and one-artifact grant approval file/hash required')
            approval_path = Path(args.approval_file).resolve()
            if approval_path.parent != ROOT.resolve():
                raise ValueError('Approval must be a private file in the fixed operation directory')
            approval_raw = approval_path.read_bytes()
            if len(approval_raw) > 20000 or digest(approval_raw) != args.approval_sha256:
                raise ValueError('Approval evidence size/hash mismatch')
            approval = json.loads(approval_raw)
            required = {'paper_id','sha256','terms_version','privacy_version','accepted_terms','read_privacy','approve_exact_grant','source_reference','actual_human_answer','recorded_at'}
            if not isinstance(approval, dict) or set(approval) != required:
                raise ValueError('Approval fields do not match the exact contract')
            if approval['paper_id'] != PID or approval['sha256'] != SHA or approval['terms_version'] != a.TERMS_VERSION or approval['privacy_version'] != a.PRIVACY_VERSION:
                raise ValueError('Approval paper/hash/current terms/privacy mismatch')
            if any(approval[k] is not True for k in ('accepted_terms','read_privacy','approve_exact_grant')):
                raise ValueError('Actual human acknowledgment and exact grant confirmation are required')
            if any(not isinstance(approval[k],str) or not 10 <= len(approval[k]) <= 2000 for k in ('source_reference','actual_human_answer')):
                raise ValueError('Preserve the actual human reply and its source; do not infer assent')
            stamp = datetime.fromisoformat(approval['recorded_at'])
            if stamp.tzinfo is None or stamp > a.now() or stamp < a.now()-timedelta(days=7):
                raise ValueError('Approval must be recent and offset-aware')
        cutoff = a.iso(a.now()-timedelta(hours=24))
        recent = db.execute('SELECT COUNT(*) FROM submissions WHERE user_id=? AND created_at>=?', (owner['id'],cutoff)).fetchone()[0]
        existing = db.execute("SELECT s.id,s.sha256,s.scan_status,s.status FROM historical_revisions h JOIN submissions s ON s.id=h.submission_id WHERE h.version_id=? OR (h.binding_json LIKE ?)", (binding['version_id'],'%'+SHA+'%')).fetchall()
        inspection = {'checked_at':a.iso(), 'paper_id':PID, 'sha256':SHA, 'catalogue_binding_valid':True, 'catalogue_sha256':catalogue_hash, 'owner_id':owner['id'], 'owner_alias':owner['alias'], 'mfa_operator_ready':bool(actor), 'account_acknowledgments_match_current':account_ack_match, 'stored_account_terms_version':owner['terms_version'], 'stored_account_privacy_version':owner['privacy_version'], 'exact_artifact_human_approval_verified':approval is not None, 'terms_version':a.TERMS_VERSION, 'privacy_version':a.PRIVACY_VERSION, 'owner_deposits_last_24h':recent, 'existing_cases':[dict(x) for x in existing], 'accepted':False, 'published':False}
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
                evidence = {'owner_user_id':owner['id'], 'agent_name':'THE ERIKSSON PROGRAMME coordinator', 'agent_version':'Codex desktop exact human acknowledgment030', 'binding':binding, 'author_instruction':'Exact-PDF terms/privacy acknowledgment and limited 24-hour, one-upload historical delegation; actual human answer: '+approval['actual_human_answer'], 'source_reference':approval['source_reference']+'; exact approval SHA256 '+args.approval_sha256, 'recorded_at':approval['recorded_at'], 'scope':['revision:create','submission:receipt'], 'terms_version':approval['terms_version'], 'privacy_version':approval['privacy_version'], 'operator_authorship_confirmed':True}
                evidence_path=save('historical-authorization.json',evidence)
                result=app.test_cli_runner().invoke(args=['authorize-historical-revision',str(evidence_path)])
                if result.exit_code:
                    raise ValueError('Native historical authorization rejected: '+result.output)
                save('grant.json',json.loads(result.output))
            grant=json.loads((ROOT/'grant.json').read_bytes())
            boundary='ERIKSSON'+uuid.uuid4().hex
            body=(f'--{boundary}\r\nContent-Disposition: form-data; name="metadata"\r\nContent-Type: application/json\r\n\r\n'.encode()+json.dumps(job['metadata']).encode()+f'\r\n--{boundary}\r\nContent-Disposition: form-data; name="manuscript"; filename="flat-coarse-rank-v3.pdf"\r\nContent-Type: application/pdf\r\n\r\n'.encode()+pdf+f'\r\n--{boundary}--\r\n'.encode())
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
