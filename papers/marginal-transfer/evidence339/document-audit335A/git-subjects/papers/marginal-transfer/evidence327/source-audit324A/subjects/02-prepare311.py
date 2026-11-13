from pathlib import Path
import json,hashlib,re,shutil,subprocess,datetime
W=Path(__file__).parent;P=W/'papers/marginal-transfer';A=Path(r'D:\Datos\the-eriksson-programme\autonomia');E=A/'evidencia-311'
E.mkdir(exist_ok=False); D=P/'evidence311';D.mkdir(exist_ok=False)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def cp(src,dst):
 dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
 if h(src)!=h(dst):raise ValueError('Copy differs '+str(src))
raw=(P/'manuscript308A.tex').read_text(encoding='utf-8')
sec=(P/'background311-section.tex').read_text(encoding='utf-8')
new=raw.replace('% DOCUMENT308: grouped sources300-303 and306; exact-PDF assessment pending.','% DOCUMENT311: grouped309/310 extension; no new exact-PDF assessment yet.')
needle='External priority is unestablished. Global many-body weights are allowed;'
replacement=r'''For $k_s=(s-1)/s<K<1$, finite parity backgrounds also give collapse
under any strict tail budget above
$1+C_s(1-K)K^{s-1}$ and below two, where
$C_s=s^s/(s-1)^{s-1}$. We solve the associated scalar background
optimization, while leaving the universal spectral threshold at such
cutoffs unresolved. External priority is unestablished. Global many-body weights are allowed;'''
if new.count(needle)!=1:raise ValueError('Abstract anchor')
new=new.replace(needle,replacement)
needle=r'\section{Comparison with hyperbounded and perturbation results}'
if new.count(needle)!=1:raise ValueError('Section anchor')
new=new.replace(needle,sec+'\n\n'+needle)
new=new.replace('the finite-cutoff endpoint in Theorem~\\ref{thm:finite-tail-endpoint}.','the finite-cutoff endpoint in Theorem~\\ref{thm:finite-tail-endpoint}.\nSection~\\ref{sec:background} then optimizes finite parity backgrounds\nto extend the sub-two tail-budget collapse region below cutoff one.')
new=new.replace('Gl\\"uck~\\cite{Gluck} gives hyperboundedness criteria and uniform essential','Gl\\"uck~\\cite{Gluck}, especially Theorem~5.1, gives hyperboundedness criteria and uniform essential')
needle='Document reproduction is a separate check of exact bytes'
add=r'''The new background construction is grouped with these results because it
uses the same transfer operator, critical exponent and balanced tilt.
The complete source309A failure, corrected309B audit and source310 audit
are retained in \texttt{evidence311}, with their original contexts and
manifests. Three full third-party source captures from audit310 remain
private and are explicitly excluded from the public subset; their
original hashes are retained without implying redistribution rights.
The original v5 PDF and its complete first exact-PDF assessment, including
all six reservations, are historical evidence only. The expanded scalar
attainment discussion follows the recorded source310 audit clarification.
No v5 score is transferred to this manuscript.
'''
if new.count(needle)!=1:raise ValueError('Reproduction anchor')
new=new.replace(needle,add+needle)
needle='Any assessment attached to this manuscript must identify the exact final'
add=r'''Source309's first audit found a missing upper restriction on a floor
parameter in an additional comparison; that failed version remains
unchanged. Its corrected version was reread in the same involved auditor
context. Source310 received a separate fresh-assignment source audit;
shared provider and filesystem again preclude an independence claim.
The v5 exact-PDF review requested gpt-6-astra with high reasoning effort,
but the served backend and effort were not independently attested.
Its full report and six reservations remain bound to its original PDF,
not this revision. No numerical assessment of the present expanded PDF
has yet been incorporated or inherited.
'''
if new.count(needle)!=1:raise ValueError('Review context anchor')
new=new.replace(needle,add+needle)
needle=r'\bibitem{Aida}'
add=r'''\bibitem{BertsimasPopescu}
D. Bertsimas and I. Popescu,
Optimal Inequalities in Probability Theory: A Convex Optimization Approach,
\emph{SIAM Journal on Optimization} \textbf{15}(3) (2005), 780--804.
\href{https://doi.org/10.1137/S1052623401399903}{Publisher version}.
'''
new=new.replace(needle,add+needle)
prior_proofs=re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}',raw,re.S)
new_proofs=re.findall(r'\\begin\{proof\}(.*?)\\end\{proof\}',new,re.S)
if len(prior_proofs)!=19 or new_proofs[:19]!=prior_proofs or len(new_proofs)!=21:raise ValueError('Existing proof mismatch/count')
(P/'manuscript311A.tex').write_text(new,encoding='utf-8',newline='\n')
for name in ['source-audit309A','source-audit309B']:
 shutil.copytree(A/'evidencia-309'/name,D/name)
excluded={'primary-bertsimas-popescu.pdf','primary-gluck-v6.html','primary-mos-v5.html'}
src=A/'evidencia-310/source-audit310A';omitted=[]
for f in sorted(src.rglob('*')):
 if not f.is_file():continue
 rel=f.relative_to(src)
 if rel.as_posix() in excluded:omitted.append({'path':rel.as_posix(),'bytes':f.stat().st_size,'raw_sha256':h(f),'reason':'Third-party complete primary-source capture; private, not redistributed'})
 else:cp(f,D/'source-audit310A'/rel)
if len(omitted)!=3:raise ValueError('Exclusion count')
for name in ['parent-source310-acceptance.json','pr257-premerge-verified.json']:cp(A/'evidencia-310'/name,D/name)
cp(A/'evidencia-309/source309-closure.json',D/'source309-closure.json')
src=A/'evidencia-308/assessment308-first-round';target=D/'historical-exact308'
for f in (src/'outputs').iterdir():
 if f.is_file():cp(f,target/'outputs'/f.name)
cp(src/'input-manifest.json',target/'original-input-manifest.json')
cp(A/'evidencia-308/author-response308.md',target/'author-response308.md')
cp(A/'evidencia-308/parent-exact-assessment308-acceptance.json',target/'parent-exact-assessment308-acceptance.json')
pdf=A/'evidencia-308/public-release-readback/ARR-2026-7KV9Y9ASX48H7A7N-v5.pdf'
if h(pdf)!='450b6afa4e49a34f5fa36958b36b302ad1e266832aa271f857522aecfd3c6444':raise ValueError('Historical PDF mismatch')
cp(pdf,target/pdf.name)
cp(A/'evidencia-308/public-release308-verified.json',target/'public-release308-verified.json')
for rel in ['research/background310/background310A.txt','research/parity-tail309/parity-tail309B.txt','papers/marginal-transfer/judges309.txt','papers/marginal-transfer/judges310.txt']:
 source=W/rel
 if not source.is_file():raise ValueError('Missing exact source '+rel)
 cp(source,D/'source-inputs'/source.name)
boundary={'scope':'New grouped311 manuscript source, not compiled or assessed. All19 prior308 proof environments unchanged; two added proof environments. Exact historical308 review and six reservations do not transfer. Full309 A/B and310 analytical reports/context/assignments preserved.','excluded310_primary_sources':omitted,'historical308_packet':'Original input-manifest preserved. Complete report/context/assignment and exact old PDF copied; remaining original review inputs remain in the immutable public v5 release and local evidencia308. No claim that this historical subset is the whole review input packet.','inherited_evidence':'Existing evidence295--308 and their original declared public subsets remain in the same repository tree. No credentials, private submission jobs or new complete third-party texts included.'}
(P/'PACKAGE-BOUNDARY311.json').write_text(json.dumps(boundary,indent=2)+'\n',encoding='utf-8')
rows=[{'path':f.relative_to(P).as_posix(),'bytes':f.stat().st_size,'raw_sha256':h(f)} for f in sorted(P.rglob('*')) if f.is_file() and f.name!='SOURCE-INPUTS311.json']
(P/'SOURCE-INPUTS311.json').write_text(json.dumps({'judges_commit':'b7d1fc093e5aef060cae757e99fe4792e96fcfac','base_commit':'ff4068b4ebfab156fddf635a12ae1d5637470afd','representation':'Raw checkout bytes, no normalization. Immutable nested evidence kept with its original line endings.','files':rows},indent=2)+'\n',encoding='utf-8')
for name in ['judges311.txt','manuscript311A.tex','background311-section.tex','PACKAGE-BOUNDARY311.json','SOURCE-INPUTS311.json']:cp(P/name,E/name)
cp(Path(__file__),E/Path(__file__).name)
print(json.dumps({'manuscript_sha256':h(P/'manuscript311A.tex'),'bytes':(P/'manuscript311A.tex').stat().st_size,'input_bindings':len(rows),'old_proofs_unchanged':19,'total_proofs':21,'private_exclusions':3}))
