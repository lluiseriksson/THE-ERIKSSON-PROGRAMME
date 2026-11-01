"""Read-only exact-v4 classification diagnostic on the existing AIRR host."""
import json
import sys
from pathlib import Path
sys.path.insert(0, '/opt/airr-intake/current')
from services.intake import app as a
root=Path('/srv/airr-private/eriksson-v4-20261031')
job=json.loads((root/'revision-job.json').read_bytes())
binding=json.loads((root/'binding.json').read_bytes())
if binding['sha256']!='e5e9ddcf044ddcfab0e4cae8e2c6ac1a3dca39ff21bf23b20989aaff4b220e05':
    raise ValueError('Unexpected artifact')
app=a.create_app()
with app.app_context():
    result={}
    for label,subject in [('original',job['metadata']['primary_subject']),('prior_verified_subject','eu-2ba1c7ad-2532-4cd7-8c5c-60f090a8700a')]:
        try:
            classification=a.validate_classification(subject,[],job['metadata']['specific_topic'])
            result[label]={'valid':True,'subject':subject,'classification':classification}
        except ValueError as error:
            result[label]={'valid':False,'subject':subject,'error':str(error)}
    rows=a.get_db().execute('SELECT s.id,s.sha256,s.status FROM historical_revisions h JOIN submissions s ON s.id=h.submission_id WHERE h.version_id=?',(binding['version_id'],)).fetchall()
    result['existing_exact_cases']=[dict(r) for r in rows]
    result['post_sent']=False
    raw=json.dumps(result,ensure_ascii=False,indent=2)
    (root/'classification-diagnostic.json').write_text(raw)
    print(raw,flush=True)