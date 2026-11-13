from pathlib import Path
import json, hashlib, shutil, re, subprocess
W=Path(__file__).parent; P=W/'papers/marginal-transfer'
A=Path(r'D:\Datos\the-eriksson-programme\autonomia'); E=A/'evidencia-314'
E.mkdir(exist_ok=False); D=P/'evidence314'; D.mkdir(exist_ok=False)
def h(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def cp(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
 if h(src)!=h(dst):raise ValueError('Copy mismatch '+str(src))
raw=(P/'manuscript311A.tex').read_bytes().decode('utf-8')
sec=(P/'endpoint314-section.tex').read_bytes().decode('utf-8')
new=raw.replace('% DOCUMENT311: grouped309/310 extension; no new exact-PDF assessment yet.','% DOCUMENT314: grouped attained-cutoff extension; exact-new-PDF assessment pending.')
def replace_once(old,replacement):
 global new
 if new.count(old)!=1:raise ValueError('Anchor count '+old[:80])
 new=new.replace(old,replacement)
replace_once('under any strict tail budget above\n$1+C_s(1-K)K^{s-1}$ and below two, where',
 'at the attained tail budget $1+C_s(1-K)K^{s-1}<2$,\nwith density floor exactly at least $K$, where')
replace_once('The final section gives a sufficient','The critical-tail section gives a sufficient')
replace_once('to extend the sub-two tail-budget collapse region below cutoff one.',
 'to extend the sub-two tail-budget collapse region below cutoff one.\nSection~\\ref{sec:attained-cutoff} attains the constructive budget\nand allows the floor to equal the cutoff.')
replace_once('The equality budget, the intervening interval and the floor $b=K$\nremain unclassified here.',
 'Theorem~\\ref{thm:attained-cutoff} below attains this constructive\nbudget with floor $b=K$; the intervening universal interval remains\nunclassified.')
replace_once(r'\section{Comparison with hyperbounded and perturbation results}',sec+'\n\n'+r'\section{Comparison with hyperbounded and perturbation results}')
# Define the old density shorthand outside every preserved proof/statement.
replace_once('$Q=P_{\\sqrt\\rho}$ and $T_r=M_{\\sqrt r}P_\\rho M_{\\sqrt r}$, where',
 '$Q=P_{\\sqrt\\rho}$ and $T_r=M_{\\sqrt r}P_\\rho M_{\\sqrt r}$.\nWe also use $\\gap(r):=\\gap(T_r)$ when the density shorthand is convenient.\nHere')
replace_once('Document reproduction is a separate check of exact bytes',r'''The attained-cutoff construction is retained as source313, with its
complete analytical report, assignment, context and byte manifests in
\texttt{evidence314}. It removes two restrictions of the preceding
construction by clipping the tilt, compensating its mean only on the
high sector, and reserving amplitude for finite tail errors.
The source311 document and production-runner audits are also retained;
that intermediate manuscript was not compiled or given a PDF score.
A redundant complete frozen311 source archive remains private on D;
the public subset declares its exact hash and original Git source, while
retaining the full reports and original manifest. No report is shortened.
Document reproduction is a separate check of exact bytes''')
replace_once('Any assessment attached to this manuscript must identify the exact final',r'''Source313 received a separate fresh-assignment analytical audit. Its
reader checked the inherited explicit balanced family rather than relying
on previous acceptance labels. The shared provider and filesystem again
do not establish independence. Its minor request to bracket each
normalized product factor is incorporated here. The prior311 document
audit's notation and navigation observations are also addressed, with all
twenty-one prior proofs and twenty prior statement environments preserved.
None of these source checks is an exact-PDF assessment or human review.
Any assessment attached to this manuscript must identify the exact final''')
prior=re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}',raw,re.S)
after=re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}',new,re.S)
if len(prior)!=21 or after[:21]!=prior or len(after)!=22:raise ValueError('Proof preservation')
pat=r'\\begin\{(theorem|lemma|proposition|corollary|remark)\}(.*?)\\end\{\1\}'
statements=re.findall(pat,raw,re.S);newstatements=re.findall(pat,new,re.S)
if len(statements)!=20 or newstatements[:20]!=statements or len(newstatements)!=21:raise ValueError('Statement preservation')
(P/'manuscript314A.tex').write_bytes(new.encode('utf-8'))
omitted=[]
for rel in ['evidencia-311/document-audit311A','evidencia-311/production-a-source-audit','evidencia-313/source-audit313A']:
 src=A/rel
 for f in sorted(src.rglob('*')):
  if not f.is_file():continue
  r=f.relative_to(src)
  if r.as_posix()=='frozen311.raw-git.zip':
   omitted.append({'audit':src.name,'path':r.as_posix(),'bytes':f.stat().st_size,'raw_sha256':h(f),'reason':'Redundant full frozen Git source archive; exact original remains on D. Source commit 8a961dceb8e21687f3ed3325051a618a425279c5 and complete original manifest/reports retained.'})
  else:cp(f,D/src.name/r)
if len(omitted)!=1:raise ValueError('Archive exclusion count')
for rel in ['evidencia-311/parent-document311-acceptance.json','evidencia-311/parent-production311-acceptance.json','evidencia-313/parent-source313-acceptance.json']:
 cp(A/rel,D/Path(rel).name)
for rel in ['research/cutoff-floor313/cutoff-floor313A.txt','papers/marginal-transfer/judges313.txt']:
 data=subprocess.check_output(['git','show','a4d0736b57eb27ce7ae7de479d62df2bc2edb6b0:'+rel],cwd=W)
 target=D/'source-inputs'/Path(rel).name;target.parent.mkdir(exist_ok=True);target.write_bytes(data)
boundary={'scope':'Grouped314 manuscript; no new PDF or score. Complete313 source report/context/assignment and original manifests; complete311 document and engineering reports retained. All21 old proofs/20 statements unchanged.','new_exclusions':omitted,'inherited_boundary':'PACKAGE-BOUNDARY311.json remains exact: three complete third-party primary-source captures excluded and historical308 input subset explicitly declared. No new third-party full text, credential or private submission payload.','archival_scope':'Original private audit packets remain complete on D. Public evidence subsets are not claimed to be complete copies of those packets.'}
(P/'PACKAGE-BOUNDARY314.json').write_text(json.dumps(boundary,indent=2)+'\n',encoding='utf-8',newline='\n')
rows=[{'path':f.relative_to(P).as_posix(),'bytes':f.stat().st_size,'raw_sha256':h(f)} for f in sorted(P.rglob('*')) if f.is_file() and f.name!='SOURCE-INPUTS314.json']
(P/'SOURCE-INPUTS314.json').write_text(json.dumps({'judges_commit':'f4214ec21','parent_manuscript_commit':'8a961dceb8e21687f3ed3325051a618a425279c5','new_theorem_commit':'a4d0736b57eb27ce7ae7de479d62df2bc2edb6b0','representation':'Exact raw file bytes; no normalization; preserved nested historical representations.','files':rows},indent=2)+'\n',encoding='utf-8',newline='\n')
for name in ['judges314.txt','endpoint314-section.tex','manuscript314A.tex','PACKAGE-BOUNDARY314.json','SOURCE-INPUTS314.json']:cp(P/name,E/name)
cp(Path(__file__),E/Path(__file__).name)
print(json.dumps({'manuscript_sha256':h(P/'manuscript314A.tex'),'bytes':(P/'manuscript314A.tex').stat().st_size,'bindings':len(rows),'old_proofs_unchanged':21,'proofs':22,'old_statements_unchanged':20,'new_exclusions':len(omitted)}))
