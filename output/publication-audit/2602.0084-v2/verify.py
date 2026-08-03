#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, re, subprocess, sys
from pathlib import Path
from PIL import Image, ImageChops
from pypdf import PdfReader
ROOT=Path(__file__).resolve().parent; ART=ROOT/'artifacts'; INPUT=ROOT/'inputs'/'2602.0084v1-public.pdf'; POP=Path(r'C:\Users\lluis\.cache\codex-runtimes\codex-primary-runtime\dependencies\native\poppler\Library\bin')
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
 r=json.loads((ART/'build-result.json').read_text(encoding='utf-8')); final=ART/r['final_pdf']; check(final.is_file() and sha(final)==r['final_sha256'],'final exists and SHA'); check(sha(INPUT)=='633c08d3f3528b60cdbcaf0d13c257aa49f6df68f4717802170dc50beeb52211','public v1 SHA'); reader=PdfReader(str(final),strict=True); check(not reader.is_encrypted and len(reader.pages)==21,'final unencrypted 21 pages')
 boxes=[(round(float(p.mediabox.width),3),round(float(p.mediabox.height),3)) for p in reader.pages]; check(len(set(boxes))==1 and 611.9 < boxes[0][0] < 612.1 and 791.9 < boxes[0][1] < 792.1,'all 21 MediaBoxes are US Letter')
 active=(ROOT/'src'/'erratum_2602_0084.tex').read_text(encoding='utf-8')+(ROOT/'SUBMISSION-ID.txt').read_text(encoding='utf-8'); flat=re.sub(r'\s+',' ',active)
 for phrase in ('principal results of version 1 are withdrawn','Defects A-G are included','Lemma 3.3 is false as printed','Nothing in this note proves the intended almost-reflection-positivity conclusion false'): check(phrase.lower() in flat.lower(),f'scope phrase: {phrase}')
 check('Lemma 3.3, the linear propagation Lemma 3.5 and Theorem 4.1 are unaffected' not in active,'stale Lemma 3.3 claim absent'); check('as'+'sert ' not in Path(__file__).read_text(encoding='utf-8'),'no assertion statements')
 qa=ART/f'qa-o{level}'; fd=qa/'final'; od=qa/'input'; fd.mkdir(parents=True,exist_ok=True); od.mkdir(parents=True,exist_ok=True)
 for d in (fd,od):
  for p in d.glob('*.png'):p.unlink()
 for pdf,d in ((final,fd),(INPUT,od)):
  run=subprocess.run([str(POP/'pdftoppm.exe'),'-r','120','-png',str(pdf),str(d/'page')],stdout=subprocess.PIPE,stderr=subprocess.PIPE); check(run.returncode==0,f'render {pdf.name}')
 fp=sorted(fd.glob('*.png')); op=sorted(od.glob('*.png')); check(len(fp)==21 and len(op)==15,'rendered page counts')
 for i,old in enumerate(op):
  with Image.open(fp[i+6]).convert('RGB') as a,Image.open(old).convert('RGB') as b: check(a.size==b.size and ImageChops.difference(a,b).getbbox() is None,f'final page {i+7} pixel-equals public v1 page {i+1}')
 fonts=subprocess.run(['pdffonts',str(final)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE); check(fonts.returncode==0 and not re.search(r'\bno\s+(?:yes|no)\s+(?:yes|no)\s+\d+',fonts.stdout),'font inventory readable and embedded')
 lines += ['STATUS SELF-VERIFIED-NOT-INDEPENDENT',f'FINAL {final.name}',f'SHA256 {sha(final)}']; (ART/f'VERIFY-TRANSCRIPT-O{level}.txt').write_text('\n'.join(lines)+'\n',encoding='utf-8',newline='\n'); print('\n'.join(lines)); return 0
if __name__=='__main__':
 try: raise SystemExit(main())
 except Exception as exc: print(f'VERIFY FAILED: {exc}',file=sys.stderr); raise
