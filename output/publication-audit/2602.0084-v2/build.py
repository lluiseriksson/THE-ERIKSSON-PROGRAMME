#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, os, subprocess, sys
from pathlib import Path
from pypdf import PdfReader, PdfWriter

ROOT=Path(__file__).resolve().parent; SRC=ROOT/'src'; INPUTS=ROOT/'inputs'; ART=ROOT/'artifacts'; JOB='erratum_2602_0084'
def sha(p: Path) -> str:
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()
def main() -> int:
    ART.mkdir(parents=True,exist_ok=True); env=dict(os.environ); env['SOURCE_DATE_EPOCH']='1785528000'; transcript=[]
    cmd=['pdflatex','-interaction=nonstopmode','-halt-on-error',f'-jobname={JOB}',f'-output-directory={ART}','erratum_2602_0084.tex']
    for n in (1,2):
        r=subprocess.run(cmd,cwd=SRC,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT); transcript.append(f'=== PDFLATEX PASS {n} ===\n{r.stdout}')
        if r.returncode: raise RuntimeError(f'pdflatex pass {n} failed')
    log=(ART/f'{JOB}.log').read_text(encoding='utf-8',errors='replace')
    if 'Overfull \\hbox' in log or 'Overfull \\vbox' in log: raise RuntimeError('overfull box')
    front=ART/f'{JOB}.pdf'; old=INPUTS/'2602.0084v1-public.pdf'; w=PdfWriter(); w.append(str(front)); w.append(str(old)); w.add_metadata({'/Title':'Retraction of Theorem 4.4 and Proposition 3.8, and Status Note (v2)','/Author':'Lluis Eriksson','/Subject':'Replacement of ai.viXra:2602.0084'})
    provisional=ART/'2602.0084v2.pdf'
    with provisional.open('wb') as f: w.write(f)
    digest=sha(provisional); pages=len(PdfReader(str(provisional)).pages); final=ART/f'2602.0084v2-{digest[:8]}-{pages}pp.pdf'
    if final.exists(): final.unlink()
    provisional.replace(final)
    result={'status':'BUILT-NOT-INDEPENDENTLY-AUDITED','final_pdf':final.name,'final_sha256':digest,'pages':pages,'erratum_pages':len(PdfReader(str(front)).pages),'public_v1_pages':len(PdfReader(str(old)).pages),'public_v1_sha256':sha(old),'source_sha256':sha(SRC/'erratum_2602_0084.tex')}
    (ART/'build-result.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n'); transcript.append('=== BUILD RESULT ===\n'+json.dumps(result,indent=2)); (ART/'BUILD-TRANSCRIPT.txt').write_text('\n\n'.join(transcript)+'\n',encoding='utf-8',newline='\n'); print(json.dumps(result,indent=2)); return 0
if __name__=='__main__':
    try: raise SystemExit(main())
    except Exception as exc: print(f'BUILD FAILED: {exc}',file=sys.stderr); raise
