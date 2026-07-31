#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, re, subprocess, sys
from pathlib import Path
from PIL import Image, ImageChops
from pypdf import PdfReader
ROOT=Path(__file__).resolve().parent; ART=ROOT/'artifacts'; INPUT=ROOT/'inputs'/'2602.0085v1-public.pdf'; POP=Path(r'C:\Users\lluis\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\poppler\Library\bin')
def sha(p:Path)->str:
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
def main()->int:
 level=sys.flags.optimize; lines=[f'PYTHON_OPTIMIZE_LEVEL {level}']
 def check(v:bool,label:str)->None:
  if not v: raise RuntimeError(label)
  lines.append('PASS '+label)
 r=json.loads((ART/'build-result.json').read_text(encoding='utf-8')); final=ART/r['final_pdf']; check(final.is_file() and sha(final)==r['final_sha256'],'final exists and SHA'); check(sha(INPUT)=='930e7ea90a21b78a71fe73bfcc48519b0ee17c66f9fe23bdf7fead21829dfd8d','public v1 SHA'); reader=PdfReader(str(final),strict=True); check(not reader.is_encrypted and len(reader.pages)==26,'final unencrypted 26 pages')
 active=(ROOT/'src'/'erratum_2602_0085.tex').read_text(encoding='utf-8')+(ROOT/'SUBMISSION-ID.txt').read_text(encoding='utf-8'); flat=re.sub(r'\s+',' ',active)
 for phrase in ('principal results of version 1 are withdrawn','Lemma 3.2 is only recoverable','original instantiation is withdrawn','Reflection positivity, Osterwalder-Schrader reconstruction, thermodynamic limit and mass gap remain open'): check(phrase.lower() in flat.lower(),f'scope phrase: {phrase}')
 check('Lemma 2.2, Lemma 3.2 and Proposition 1.3 are unaffected' not in active,'stale Lemma 3.2 claim absent'); check('as'+'sert ' not in Path(__file__).read_text(encoding='utf-8'),'no assertion statements')
 qa=ART/f'qa-o{level}'; fd=qa/'final'; od=qa/'input'; fd.mkdir(parents=True,exist_ok=True); od.mkdir(parents=True,exist_ok=True)
 for d in (fd,od):
  for p in d.glob('*.png'):p.unlink()
 for pdf,d in ((final,fd),(INPUT,od)):
  run=subprocess.run([str(POP/'pdftoppm.exe'),'-r','120','-png',str(pdf),str(d/'page')],stdout=subprocess.PIPE,stderr=subprocess.PIPE); check(run.returncode==0,f'render {pdf.name}')
 fp=sorted(fd.glob('*.png')); op=sorted(od.glob('*.png')); check(len(fp)==26 and len(op)==21,'rendered page counts')
 for i,old in enumerate(op):
  with Image.open(fp[i+5]).convert('RGB') as a,Image.open(old).convert('RGB') as b: check(a.size==b.size and ImageChops.difference(a,b).getbbox() is None,f'final page {i+6} pixel-equals public v1 page {i+1}')
 fonts=subprocess.run(['pdffonts',str(final)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE); check(fonts.returncode==0 and not re.search(r'\bno\s+(?:yes|no)\s+(?:yes|no)\s+\d+',fonts.stdout),'font inventory readable and embedded')
 lines += ['STATUS SELF-VERIFIED-NOT-INDEPENDENT',f'FINAL {final.name}',f'SHA256 {sha(final)}']; (ART/f'VERIFY-TRANSCRIPT-O{level}.txt').write_text('\n'.join(lines)+'\n',encoding='utf-8',newline='\n'); print('\n'.join(lines)); return 0
if __name__=='__main__':
 try: raise SystemExit(main())
 except Exception as exc: print(f'VERIFY FAILED: {exc}',file=sys.stderr); raise
