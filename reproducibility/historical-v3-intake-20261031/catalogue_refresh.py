"""Prepare/apply one reviewed catalogue entry through the documented operator path.
No grant, submission, policy, user, quota or editorial decision is created here.
Apply requires separately recorded action-time human approval of this change.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import urllib.request
import uuid

PID='ARR-2026-7EPM3V3DP796BBRR'
ENTRY={'record_id':'arr:record:eeb507b1-b6c7-4996-bc62-a4e7c416be00',
       'version_id':'arr:version:1047e4db-2050-4f7f-9f41-9c526bdbe570',
       'version':'v2','canonical_sha256':'b37f2fe86b7a8a526ad02f8b28491c300a9ff72d5653536bc5532e8c9468ed8f',
       'authors':['Lluis Eriksson']}
BEFORE={'record_id':'arr:record:eeb507b1-b6c7-4996-bc62-a4e7c416be00',
       'version_id':'arr:version:44c1db02-4eae-4b1c-ba2a-bb5d6b994c97',
       'version':'v1','canonical_sha256':'48b2b725422263a272d9862621fa723d3d82c9d186dd7151be39c6ff1e3ff2e7',
       'authors':['Lluis Eriksson']}
ROOT=Path('/srv/airr-private/eriksson-v3-20261031')
EXPECTED=Path('/srv/airr-private/historical-revisions/catalogue.json')


def main():
    p=argparse.ArgumentParser()
    p.add_argument('mode',choices=['inspect','apply'])
    p.add_argument('--approval-evidence',type=Path)
    args=p.parse_args()
    if os.getuid()!=0:
        raise ValueError('Existing authenticated operator host required')
    os.umask(0o077)
    sys.path.insert(0,'/opt/airr-intake/current')
    from services.intake import app as a
    from services.intake.historical_revisions import catalogue
    app=a.create_app()
    with app.app_context():
        entries,old_hash=catalogue(app)
        path=Path(app.config['HISTORICAL_REVISION_CATALOGUE'])
        if path!=EXPECTED or path.is_symlink():
            raise ValueError('Unexpected catalogue path; no mutation')
        if app.config.get('HISTORICAL_OPERATOR_AUTHOR')!='Lluis Eriksson':
            raise ValueError('Configured author mismatch')
        actor=a.get_db().execute("SELECT id FROM users WHERE email=? AND role='operator' AND active=1 AND totp_secret IS NOT NULL",(app.config['OPERATOR_EMAIL'],)).fetchone()
        if not actor:
            raise ValueError('Existing active MFA operator required')
        pending=a.get_db().execute("SELECT COUNT(*) FROM historical_revision_grants h JOIN agent_grants g ON g.id=h.grant_id WHERE g.state='approved' AND g.expires_at>? AND g.uses=0",(a.iso(),)).fetchone()[0]
        if pending:
            raise ValueError('Existing unconsumed historical grant would be invalidated; no catalogue change')
        if entries.get(PID) != BEFORE:
            raise ValueError('Expected exact old v1 entry absent; reconcile instead of modifying')
        html=urllib.request.urlopen('https://airr.science/papers/'+PID+'/',timeout=25).read().decode()
        for value in (ENTRY['record_id'],ENTRY['version_id'],ENTRY['canonical_sha256']):
            if value not in html:
                raise ValueError('Live public parent identity/hash mismatch')
        versions=set(re.findall(PID+r'/versions/v(\d+)/',html))
        if not versions or max(map(int,versions)) != 2:
            raise ValueError('Unexpected latest public version')
        result={'observed_utc':a.iso(),'paper_id':PID,'before':BEFORE,'after':ENTRY,'before_sha256':old_hash,'unconsumed_unexpired_historical_grants':pending,'public_parent_matches':True,'applied':False}
        if args.mode=='inspect':
            (ROOT/'catalogue-refresh-inspection.json').write_text(json.dumps(result,indent=2))
            print(json.dumps(result),flush=True)
            return
        if not args.approval_evidence:
            raise ValueError('Separate human action-time approval record required')
        approval=json.loads(args.approval_evidence.read_bytes())
        if approval.get('paper_id')!=PID or approval.get('sha256')!='c9de923a66038ed66c3f68ecf8256b3f738a3ccf27e41f77e470bf7dc3efb5b9' or approval.get('only_existing_predecessor_refresh') is not True or len(approval.get('actual_human_answer',''))<2:
            raise ValueError('Missing actual action-time human approval')
        prior=json.loads((ROOT/'catalogue-refresh-inspection.json').read_bytes())
        if prior['before_sha256']!=old_hash:
            raise ValueError('Catalogue changed since diagnosis; refresh review before mutation')
        raw=path.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=old_hash:
            raise ValueError('Catalogue changed during inspection')
        stat=path.stat()
        backup=ROOT/('catalogue-before-'+old_hash+'.json')
        if not backup.exists():
            with backup.open('xb') as f:
                os.fchmod(f.fileno(),0o600)
                f.write(raw)
        updated=dict(entries)
        updated[PID]=ENTRY
        if {k:v for k,v in updated.items() if k!=PID}!={k:v for k,v in entries.items() if k!=PID}:
            raise ValueError('Unexpected non-target change')
        payload=(json.dumps(updated,ensure_ascii=False,indent=2)+'\n').encode()
        temporary=path.with_name(path.name+'.eriksson-'+uuid.uuid4().hex)
        with temporary.open('xb') as f:
            os.fchmod(f.fileno(),stat.st_mode & 0o777)
            os.fchown(f.fileno(),stat.st_uid,stat.st_gid)
            f.write(payload)
            f.flush()
            os.fsync(f.fileno())
        if hashlib.sha256(path.read_bytes()).hexdigest()!=old_hash:
            raise ValueError('Catalogue changed before atomic replacement; no replacement')
        os.replace(temporary,path)
        final,new_hash=catalogue(app)
        if final!=updated:
            raise ValueError('Post-write catalogue mismatch; preserve evidence and stop')
        result.update(applied=True,after_sha256=new_hash,backup=str(backup),approval_evidence_sha256=hashlib.sha256(args.approval_evidence.read_bytes()).hexdigest())
        (ROOT/'catalogue-refresh-receipt.json').write_text(json.dumps(result,indent=2))
        os.chmod(ROOT/'catalogue-refresh-receipt.json',0o600)
        print(json.dumps(result),flush=True)


if __name__=='__main__':
    try:
        main()
    except Exception as e:
        print(json.dumps({'error_type':type(e).__name__,'error':str(e),'no_automatic_retry':True}),flush=True)
        raise SystemExit(1)
