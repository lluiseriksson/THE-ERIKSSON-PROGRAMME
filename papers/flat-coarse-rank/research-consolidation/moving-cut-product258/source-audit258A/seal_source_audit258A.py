import pathlib,subprocess,hashlib,json,datetime,shutil
W=pathlib.Path(r'C:\Trabajo\the-eriksson-programme\perron-spec-210-20261108')
D=pathlib.Path(r'D:\Datos\the-eriksson-programme\autonomia\evidencia-258\source-audit258A')
commit='d7840f33a5e20120565f3d5803dfabb32802de95'
path='papers/flat-coarse-rank/research-consolidation/moving-cut-product258/bounded-matching-obstruction258A.txt'
depcommit='fed201fd10f952a04e638c324dc0e1359711911a'
deppath='papers/flat-coarse-rank/research-consolidation/fixed-cut-product257/capacity-class-obstruction257A.txt'
def digest(raw):return hashlib.sha256(raw).hexdigest()
def need(b,m):
    if not b:raise RuntimeError(m)
def git(*args):return subprocess.run(['git','-C',str(W),*args],check=True,capture_output=True).stdout
raw=git('show',commit+':'+path);dep=git('show',depcommit+':'+deppath)
need(digest(raw)=='0c99070cdea4a3c7edf7168a8dfd2eb6eca96b08ed21e5002c003424ee7d66dc','258 raw Git hash mismatch')
need(digest(dep)=='8b92c1aeae67c26832cdd4e53dfcfb62537640d3d2a0a96370e677c3cd1ddbbc','257 raw Git hash mismatch')
need((W/path).read_bytes()==raw,'258 working copy differs from audited Git')
need((W/deppath).read_bytes()==dep,'257 working copy differs from imported Git')
blob=git('rev-parse',commit+':'+path).decode().strip()
need(blob=='e48129257476ed9cae22b45aa5800b2cd1ef354f','258 Git blob mismatch')
need(not D.exists(),'Audit directory already exists; do not overwrite')
(D/'subjects').mkdir(parents=True)
subjects=[]
def subject(name,data,source,scope):
    p=D/'subjects'/name;p.write_bytes(data)
    subjects.append({'path':p.relative_to(D).as_posix(),'bytes':len(data),'sha256_raw':digest(data),'source':source,'read_scope':scope,'representation':'Exact raw bytes, no normalization'})
subject('bounded-matching-obstruction258A.txt',raw,commit+':'+path,'Entire proof read and analytically rederived')
subject('capacity-class-obstruction257A.txt',dep,depcommit+':'+deppath,'Section3 one-corner cutoff lemma directly relied upon and rederived; full raw source retained as context; no prior audit verdict imported')
subject('OPERATIONAL-GOVERNANCE-CHARTER.md',(W/'docs/OPERATIONAL-GOVERNANCE-CHARTER.md').read_bytes(),str(W/'docs/OPERATIONAL-GOVERNANCE-CHARTER.md'),'Entire charter directly read')
subject('CLAUDE.md',(W/'CLAUDE.md').read_bytes(),str(W/'CLAUDE.md'),'First75 lines directly read; full raw file retained as governance context')
prompt=r'''Mandatory separate exact-source analytical audit under repository charter §4. Audit frozen commit d7840f33a5e20120565f3d5803dfabb32802de95 in C:\Trabajo\the-eriksson-programme\perron-spec-210-20261108; file papers/flat-coarse-rank/research-consolidation/moving-cut-product258/bounded-matching-obstruction258A.txt raw SHA256 0c99070cdea4a3c7edf7168a8dfd2eb6eca96b08ed21e5002c003424ee7d66dc. Full adversarial derivation: moving product partitions with constant q but independently varying cuts/factor counts; cyclic adjacent corner bijections need no global labels or common translation; min-cutoff interslice inequality; convolution shifts r1=0,1 including time seam; actual real coexact preimage, exact means, nonzero norm, original source weights; all constants; bottleneck B_* quantified recovery tradeoff and sqrt(log n) necessary speed inference. Re-read and verify imported one-corner cutoff lemma from257A at fed201fd10f952a04e638c324dc0e1359711911a raw8b92c1aeae67c26832cdd4e53dfcfb62537640d3d2a0a96370e677c3cd1ddbbc, not inherit its verdict. Preserve all limitations or failures. No source edits, commits, PR, desktop/browserUI, Colab runtime, Windows mathematical computation/compile; reasoning/file/git/hash only. Capture all directly read proof/governance subjects plus complete original report, assignment, model/context and raw manifest in D:\Datos\the-eriksson-programme\autonomia\evidencia-258\source-audit258A. No scores, formal/numerical/peer review or independence claim. Same involved Codex/OpenAI GPT6family exposed; exactbackend/version/effort unknown; parentcontextvisibility disclosed. No PR/body exists at assignment; bodycapture N/A. I will send no inbound messages while you audit. No disposable clone required. Return complete verdict, sourceblob, fullreport/manifest paths/hash/count. Acceptance decisions must use explicit checks, no Python asserts.'''
(D/'prompt.txt').write_text(prompt+'\n',encoding='utf-8')
report='''258A EXACT-SOURCE ANALYTICAL AUDIT — COMPLETE ORIGINAL REPORT
11 November 2026

VERDICT: ACCEPT_ANALYTICAL_OBSTRUCTION_FOR_BOUNDED_MATCHING_PRODUCT_SLICES_ONLY.
Exact frozen source: d7840f33a5e20120565f3d5803dfabb32802de95.
Proof raw-byte SHA256:
0c99070cdea4a3c7edf7168a8dfd2eb6eca96b08ed21e5002c003424ee7d66dc.
Proof Git blob: e48129257476ed9cae22b45aa5800b2cd1ef354f.
No blocking defect found in the stated finite theorem or its quantitative
search reduction. The conclusion remains restricted to the declared original
product-slice observations and bottleneck-motion tradeoff; global Q251 is OPEN.

METHOD AND DIRECT INPUTS
I read the entire258A source and analytically rederived its identities,
estimates, constants and implications. I separately re-read and checked the
one-corner cutoff lemma in257A Section3 at its exact named commit, rather
than inherit257A's audit verdict. Both complete raw mathematical sources
are captured. I read the repository governance charter and the first75
lines of CLAUDE.md; full raw governance files are retained with read scopes.
Only reasoning, file reads/copies, raw-byte hashes and Git identity reads
were used. No mathematical script, numerical enumeration, Lean/Lake,
oracle, Colab runtime or symbolic engine was run. Provenance hashes are
not mathematical or formal certificates. No PR/body existed in the audit
assignment, so body capture and normalized body hash are N/A.

1. IMPORTED ONE-CORNER CUTOFF — ACCEPT AFTER FRESH DERIVATION
For R=n/4>=8 and L=log((R+1)/3), the clipped logarithm f_p is0 for periodic
l-infinity radius<=2 and1 for radius>=R. Only edges crossing radius r to
r+1,2<=r<R, carry energy. Since r+1<=n/4, these are ordinary square
boundaries within a periodic local chart, not an antipodal distance seam.
There are8r+4<=32r crossing edges, each counted once by the forward-edge
energy, and each increment is at most1/((r+1)L). Hence the energy is bounded
by32log(R+1)/L^2<=64/L, where the last step uses R>=8.
For the deficit, split u=rho+1 into the dyadic bins specified in257A.
The kth bin has at most4(R+1)^2/4^k sites and deficit at most
(k+1)log2/L. The bound also covers the clipped inner plateau, where the
unclipped logarithmic deficit is at least1. The series is80/27<4;
therefore the norm deficit is <=16(R+1)^2/L^2<=4n^2/L^2.
The inner and outer plateau endpoints, dyadic equalities, translated center
and cyclic seam cases are covered. These bounds use no sharp capacity
constant or unproved external asymptotic theorem. The imported lemma is valid.

2. ACTUAL COEXACT PREIMAGE AND MOVING RECTANGLE MEANS — ACCEPT
For the forward curl, the23 two-form contributes -partial3^*phi=delta3phi
to component2 and partial2^*phi=-delta2phi to component3. Thus setting
phi=delta2delta3Psi and psi23=phi gives exactly the stated third-difference
P Psi in the actual image of d1^*. The potential and field are real and
periodic. Each nonzero component has a full zero sum by a transverse first
difference; no Hodge projection or replacement by mere divergence freedom
appears.
At a fixed slice, summing delta2delta3^2Psi over a product of cyclic intervals
gives the four-corner difference of delta3Psi. Summing -delta2^2delta3Psi
gives the negative four-corner difference of delta2Psi. All start-minus-one
endpoints are predecessor terminal endpoints in that slice. The formulas
hold for wrapping intervals and collapse to zero in a whole-cycle factor.
Distinct nonempty intervals have distinct terminal endpoints, so E_i has
exactly M2(i)M3(i)=q points, even when the two factor counts vary between
slices. Since eta(i,.) is0 at every corner and its backward transverse
neighbors, both required differences of etaPsi0 vanish there. No comparison
of factor counts or labels across slices is needed for this argument.
Every original component mean vanishes, and channel2 is identically0.

3. MOVING MINIMUM AND CYCLIC ADJACENT MATCHINGS — ACCEPT
At each slice, 1-eta is the maximum of q nonnegative individual deficits,
so its squared norm is at most their sum. Summing the single-center bound
over q centers and n slices yields4qV/L^2, as asserted in(2).
For a transverse displacement, telescoping a shortest integer representative
path and using the l2 triangle inequality bounds the difference of a radial
cutoff by the path length times sqrt(64/L). For matched centers p and p',
f_(p')(.+u) and f_p differ by the displacement u-(p'-p), whose representative
l1 length is at most |u|_1+B. Thus the displayed individual-center estimate
follows from a genuine translation estimate.
The minimum is1-Lipschitz in the maximum norm of finite lists. The bijection
beta_i allows the two lists at slices i and i+1 to be indexed by the SAME
q points in E_i. Squaring the pointwise maximum and bounding it by the sum
produces(4), including its linear q loss. With r1=0 the identity matching
removes B. Summing over slices gives(5) for r1=0,1.
There is no requirement to concatenate the beta_i into fixed global labels.
Only one longitudinal step is ever used. The i=n-1 to0 step is covered by
the explicitly required final cyclic matching. Therefore a nontrivial
permutation after a cycle, independent deformation and changing product
factor counts do not invalidate the estimate. Conversely, (5) is not silently
extended to long longitudinal shifts or to variable cardinalities q_i.

4. ORIGINAL LOW WAVE AND SOURCE PARITY — ACCEPT
The period4 identities are delta sin=sin+cos, delta2delta3sin=2cos, and the
next difference w=(2,-2,-2,2). Thus z0=(0,w,-w) has pointwise squared norm8
and complete squared norm8V. Since4|n, this includes every periodic seam.
At odd total residue1, w(2)=w(1)=-2; at residue3, w(0)=w(3)=2. Every forward
direction advances the total residue by1. All ORIGINAL channel1 strong
forward-source differences therefore vanish exactly. The proof correctly
retains the original total-coordinate phase instead of transporting that
phase with the cut geometry.

5. LONGITUDINAL CONVOLUTION COMMUTATORS — ACCEPT
For a finite convolution, the stated commutator identity is exact term by
term. Multiplication by translated Psi0 is bounded by1. Combining that fact
with(5) and the norm triangle inequality gives(6), for precisely the shift
set r1 in{0,1}.
Both P components contain three transverse backward differences, hence
coefficient l1 bound8, transverse shift radius<=3 and r1=0. Their squared
commutator norms sum to2*(8*3)^2*64nq/L=73728nq/L.
For partial2P and partial3P, the coefficient l1 bound is16, transverse radius
at most4 and r1=0. For partial1P, the only longitudinal shifts are0 and+1,
the transverse radius is at most3, and the coefficient l1 bound is16.
Thus M=max(4,3+B) controls every radius term in(6). Repeated translations
may combine coefficients but cannot increase these conservative l1 bounds.
There are six direction/nonzero-component instances. Their squared norm
sum is bounded by6*(16M)^2*64nq/L=98304M^2nq/L.
On the ORIGINAL odd source sites, eta partial_h z0=0. Restricting the full
commutator norm bound to those sites is legitimate. This derivation neither
moves H to target sites nor treats eta as independent of x1. The B term is
exactly the needed cost for moving geometry. Smoothness of a minimum is not
assumed; finite first-difference translation bounds suffice for these finite
third/fourth-order convolution commutators.

6. NONZERO WITNESS AND WEIGHTED ENERGY CONSTANTS — ACCEPT
The two-term squared-norm bound for z1-z0 gives
16||1-eta||^2+147456nq/L. With the deficit estimate and n<=V, this is at
most(64q/L^2+147456q/L)V. Since M>=4, the declared threshold implies
L>=2^22q. For q>=1 the two error coefficients are <=2^-38 and9/256,
whose sum is strictly less than2. The reverse triangle inequality therefore
proves ||z1||>sqrt(2V), so the actual field, not merely its potential, is
nonzero.
Multiplying the strong-source sum by H=cn^2 gives98304M^2cqV/L. The threshold
bounds this by3cV/8 because98304/2^18=3/8. The strict norm lower bound then
gives strong energy <3c||z1||^2/16. Each forward difference has norm at most
2||z1||. Summing three directions bounds the weak-source part by12a||z1||^2
=c||z1||^2/4. This upper bound may overcount some sources, which is harmless.
The total is strictly less than7c||z||^2/16, stronger than the stated weak
inequality, and hence strictly below the target c. Every quadratic penalty
on the zero measurement vector is zero, including arbitrary size-dependent
coefficients. The obstruction follows in the original model and norms.

7. BOTTLE-NECK TRADEOFF AND NECESSARY SPEED — ACCEPT WITH SCOPE LIMIT
For each adjacent pair of finite q-point sets, there are finitely many
bijections, and all periodic distances are attained nonnegative integers.
Thus B_* exists as a finite integer and supplies the geometric hypothesis.
Applying the theorem conditionally at B=B_* and taking contraposition proves
L<2^18q max(4,3+B_*)^2 whenever recovery occurs. This is not a claim that the
low-energy witness exists for every B_* regardless of the threshold.
If q<=Q and L>=2^22Q, the necessary inequality forces max(4,3+B_*)>4;
otherwise it contradicts L>=2^22Q. Then3+B_*>sqrt(L/(2^18q))
>=sqrt(L/(2^18Q)), yielding exactly(12). For uniformly bounded q this is
a necessary order sqrt(log n) growth of bottleneck motion along the declared
4-divisible n. For bounded B, q must instead grow at least as log n and the
3nq full-row count has order n log n. Only these scoped implications follow.

OPEN OBJECTIONS AND LIMITATIONS — RETAIN
O1. Global Q251 remains OPEN. Rapidly jumping cutsets can make the bound
inconclusive. General canonical/nonproduct partitions, variable corner counts
between slices, and all possible coarse observation maps are not settled.
The result is an extension to a weaker quantitative geometry restriction,
not unconditional elimination of all geometry hypotheses.
O2. Originality/priority of this precise moving-cut application remains
UNESTABLISHED. The capacity/minimum/translation/commutator ingredients are
classical. I performed no primary-source equivalence or novelty search and
assign no importance from thematic connection to Yang-Mills.
O3. Constants and the threshold are enormous and nonoptimized. No numerical
construction, practical crossover or application benchmark was checked.
O4. The result is a finite counting-norm coexact obstruction; it gives no
physical spectral gap, continuum construction or change to PR29/TermSource.
O5. This is an involved Codex analytical source audit by a separate child
session, with the parent conversation and construction visible. Blindness,
model/provider/statistical independence and human peer review are not
established. Exact served backend/version/effort were not exposed; the
available identity description is Codex/OpenAI, GPT-6 family. No grade,
stars, formal verification, numerical certificate, PDF review, editorial
acceptance, publication or inherited255B assessment is supplied here.

FAILURES FOUND AND OPERATIONAL CONTEXT
No blocking algebraic, seam, matching, constant, source-weight, coexact-image,
norm or scope defect was found in the exact frozen258A source. No failed gate
was changed or prior verdict resampled. No inbound parent messages arrived
while this audit ran. No branch/source was edited, no PR/body was changed,
no disposable clone/worktree or runtime was created, and no desktop/browser
control or message to another chat/automation occurred. Cleanup is N/A.
The complete assignment and declared review context are separate artifacts.
Full inherited account conversation is not exportable by a tool; its visibility
and limits are disclosed, rather than a fictitious full transcript claimed.
'''
(D/'full-report.txt').write_text(report,encoding='utf-8')
context={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'task':'/root/moving_cut258_source_audit','verdict':'ACCEPT_ANALYTICAL_OBSTRUCTION_FOR_BOUNDED_MATCHING_PRODUCT_SLICES_ONLY','exact_commit':commit,'proof_sha256_raw':digest(raw),'proof_git_blob':blob,'dependency_commit':depcommit,'dependency_sha256_raw':digest(dep),'dependency_read_scope':'Section3 cutoff lemma freshly rederived; no prior audit verdict inherited','model_identity_exposed':'Codex/OpenAI, GPT-6 family; exact served backend/version/effort not exposed','independence':'Separate child session within same involved programme; parent conversation and construction visible; not blind or independently established','numerical_grade':None,'formal_verification':False,'numerical_experiment':False,'external_novelty_audit':False,'inbound_parent_messages_during_audit':False,'PR_body_capture':'N/A: no PR/body existed in assignment','PR_normalized_body_hash':None,'runtime_created':False,'disposable_clone_created':False,'source_or_branch_modified':False,'subject_count':len(subjects),'subjects':subjects,'review_context_limit':'Full inherited account conversation is not exportable by a tool. prompt.txt is the complete supplied assignment, not a fictitious complete account transcript.'}
(D/'review-context.json').write_text(json.dumps(context,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
shutil.copyfile(__file__,D/pathlib.Path(__file__).name)
files=[]
for p in sorted(D.rglob('*')):
    if p.is_file():files.append({'path':p.relative_to(D).as_posix(),'bytes':p.stat().st_size,'sha256_raw':digest(p.read_bytes())})
manifest={'representation':'Exact raw bytes, no normalization; manifest does not hash itself','verdict':context['verdict'],'source_commit':commit,'source_sha256_raw':digest(raw),'source_git_blob':blob,'subject_count':len(subjects),'subjects':subjects,'files':files}
(D/'hashes.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
for f in files:
    p=D/f['path'];need(p.stat().st_size==f['bytes'] and digest(p.read_bytes())==f['sha256_raw'],'Sealed file mismatch')
print(json.dumps({'verdict':context['verdict'],'subjects':len(subjects),'manifested_files':len(files),'full_report_sha256_raw':digest((D/'full-report.txt').read_bytes()),'manifest_sha256_raw':digest((D/'hashes.json').read_bytes()),'source_blob':blob,'directory':str(D)}))
