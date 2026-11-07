import base64, datetime, hashlib, json, os, platform, resource, subprocess, sys, time, traceback, zipfile
from pathlib import Path

SOURCE = 'dfc2205dcfb8642bf5639c8433e4bdbff38075a3'
if sys.platform != 'linux':
    raise RuntimeError('Scientific execution belongs only on own Colab Linux')
ROOT = Path('/content/tep185')
if ROOT.exists():
    raise RuntimeError('Own unit185 directory already exists; reconcile previous output before rerun')
ROOT.mkdir()
OUT = ROOT/'evidence'
OUT.mkdir()
START = datetime.datetime.now(datetime.timezone.utc).isoformat()
T0 = time.perf_counter()
steps = []

def run(label, args, cwd=None):
    out, err = OUT/(label+'.stdout.txt'), OUT/(label+'.stderr.txt')
    started = time.perf_counter()
    timed_out = False
    with out.open('wb') as fo, err.open('wb') as fe:
        child = subprocess.Popen(args, cwd=cwd, stdout=fo, stderr=fe)
        try:
            code = child.wait(timeout=120)
        except subprocess.TimeoutExpired:
            timed_out = True
            child.kill()
            code = child.wait()
    tmp = OUT/(label+'.exit.tmp')
    tmp.write_text(str(code)+'\n')
    os.replace(tmp, OUT/(label+'.exit.txt'))
    steps.append({'label':label,'seconds':time.perf_counter()-started,'exit_code':code,'timed_out':timed_out})
    if code != 0 or timed_out:
        raise RuntimeError('Actual child failure: '+label)
    return out.read_bytes()

report = {'unit':185,'source_sha':SOURCE,'execution_plane':'Own Colab Linux CPU/high-RAM',
          'started_at':START,'billed_compute_units':None,'clones':[],
          'scope':'Selected exact laminate matrices, interval trees and actual coexact falsifier, not an all-size or formal proof, independent review or AIRR assessment.'}
try:
    payloads = []
    workers = []
    proofs = []
    for name in ['fresh-a','fresh-b']:
        clone = ROOT/name
        run(name+'-clone',['git','clone','--depth','1','--branch','codex/tep-laminated-rectangles-20261107',
                          'https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME.git',str(clone)])
        head = run(name+'-head',['git','rev-parse','HEAD'],clone).decode().strip()
        if head != SOURCE:
            raise RuntimeError('Pinned source mismatch')
        worker = clone/'scripts/laminated_rectangles185.py'
        proof = clone/'papers/flat-coarse-rank/research/2026-11-07_laminated-rectangles185.txt'
        wh = hashlib.sha256(worker.read_bytes()).hexdigest()
        ph = hashlib.sha256(proof.read_bytes()).hexdigest()
        helper = clone/'scripts/green_moment_partition184.py'
        hh = hashlib.sha256(helper.read_bytes()).hexdigest()
        if hh != 'c58469fb3420a7c5ba83e2692c88d2335074940db317f6a14e9a199771d084a4':
            raise RuntimeError('Pinned imported helper mismatch')
        (OUT/(name+'-helper184.py')).write_bytes(helper.read_bytes())
        if wh != '0a528d029cceb0226cd36e31970b0a7275ad8f9a485aae2024392d32bb193062' or ph != 'cee3556c1ff9dd99a69b3d62b20f6528818926cca2734b2728b51ce9e4fdd407':
            raise RuntimeError('Exact worker/proof content hash mismatch')
        workers.append(wh)
        proofs.append(ph)
        (OUT/(name+'-worker.py')).write_bytes(worker.read_bytes())
        (OUT/(name+'-proof.txt')).write_bytes(proof.read_bytes())
        report['clones'].append({'name':name,'root':str(clone),'head':head,'worker_sha256':wh,'proof_sha256':ph})
        for mode in ['normal','optimized']:
            args = [sys.executable]+(['-O'] if mode == 'optimized' else [])+[str(worker)]
            raw = run(name+'-'+mode,args,clone)
            lines = raw.decode().splitlines()
            if len(lines) != 2 or not lines[1].startswith('PAYLOAD_SHA256='):
                raise RuntimeError('Unexpected worker protocol')
            payload = (lines[0]+'\n').encode()
            digest = hashlib.sha256(payload).hexdigest()
            if lines[1] != 'PAYLOAD_SHA256='+digest:
                raise RuntimeError('Payload hash mismatch')
            decoded = json.loads(lines[0])
            if (decoded['status'] != 'SELECTED_EXACT_LAMINATE_CONTROLS' or len(decoded['mutations_rejected']) != 6
                or len(decoded['psd_cases']) != 6 or len(decoded['tree_cases']) != 72 or len(decoded['layer_cases']) != 5):
                raise RuntimeError('Worker acceptance counters mismatch')
            payloads.append(payload)
    if len(set(workers)) != 1 or len(set(proofs)) != 1 or len(payloads) != 4 or len(set(payloads)) != 1:
        raise RuntimeError('Fresh source or normal/optimized payload mismatch')
    (OUT/'payload.json').write_bytes(payloads[0])
    report.update(status='SELECTED_EXACT_FINITE_CHECKS_VERIFIED',matching_payloads=4,
                  payload_sha256=hashlib.sha256(payloads[0]).hexdigest(),
                  worker_sha256=workers[0],proof_sha256=proofs[0])
except Exception as exc:
    report.update(status='FAILED',error=str(exc))
    (OUT/'failure-traceback.txt').write_text(traceback.format_exc())
finally:
    report.update(steps=steps,elapsed_seconds=time.perf_counter()-T0,
                  finished_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                  python=platform.python_version(),host_fingerprint=hashlib.sha256(platform.node().encode()).hexdigest())
    (OUT/'report.json').write_text(json.dumps(report,sort_keys=True,indent=2)+'\n')
    manifest = [{'path':p.name,'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
                for p in sorted(OUT.iterdir()) if p.is_file()]
    (OUT/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
    archive = ROOT/'tep185-evidence.zip'
    with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
        for p in sorted(OUT.iterdir()):
            z.write(p,p.name)
    raw = archive.read_bytes()
    print('REPORT185='+json.dumps(report,sort_keys=True))
    print('ZIP185_SHA256='+hashlib.sha256(raw).hexdigest())
    print('ZIP185_BYTES='+str(len(raw)))
    print('EXPORT185='+base64.b64encode(raw).decode())
