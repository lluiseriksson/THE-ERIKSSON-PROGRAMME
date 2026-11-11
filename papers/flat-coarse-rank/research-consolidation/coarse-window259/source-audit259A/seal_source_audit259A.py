import pathlib,subprocess,hashlib,json,datetime,shutil
W=pathlib.Path(r'C:\Trabajo\the-eriksson-programme\perron-spec-210-20261108')
D=pathlib.Path(r'D:\Datos\the-eriksson-programme\autonomia\evidencia-259\source-audit259A')
def need(b,m):
    if not b:raise RuntimeError(m)
def digest(raw):return hashlib.sha256(raw).hexdigest()
def gitraw(ref):return subprocess.run(['git','-C',str(W),'show',ref],capture_output=True,check=True).stdout
commit='2f370a7da850b8066a9afe95c523e49bd1ef725e'
rel='papers/flat-coarse-rank/research-consolidation/coarse-window259/coarse-window-obstruction259A.txt'
sources=[
 ('coarse-window-obstruction259A.txt',gitraw(commit+':'+rel),commit+':'+rel,'Entire proof read and analytically rederived','03c71a1a4a652a6d28bc38acc43b7a2227796a300d673e1611f65417bb50557f'),
 ('capacity-class-obstruction257A.txt',gitraw('fed201fd10f952a04e638c324dc0e1359711911a:papers/flat-coarse-rank/research-consolidation/fixed-cut-product257/capacity-class-obstruction257A.txt'),'fed201fd10f952a04e638c324dc0e1359711911a:papers/flat-coarse-rank/research-consolidation/fixed-cut-product257/capacity-class-obstruction257A.txt','Entire source read; imported Section3 cutoff lemma freshly checked; no prior verdict inherited','8b92c1aeae67c26832cdd4e53dfcfb62537640d3d2a0a96370e677c3cd1ddbbc'),
 ('bounded-matching-obstruction258A.txt',gitraw('d7840f33a5e20120565f3d5803dfabb32802de95:papers/flat-coarse-rank/research-consolidation/moving-cut-product258/bounded-matching-obstruction258A.txt'),'d7840f33a5e20120565f3d5803dfabb32802de95:papers/flat-coarse-rank/research-consolidation/moving-cut-product258/bounded-matching-obstruction258A.txt','Entire source read; conventions and commutator/norm arguments checked afresh, not previous verdict','0c99070cdea4a3c7edf7168a8dfd2eb6eca96b08ed21e5002c003424ee7d66dc'),
 ('OPERATIONAL-GOVERNANCE-CHARTER.md',(W/'docs/OPERATIONAL-GOVERNANCE-CHARTER.md').read_bytes(),str(W/'docs/OPERATIONAL-GOVERNANCE-CHARTER.md'),'Entire charter read in two consecutive portions; full local raw bytes retained',None),
 ('CLAUDE.md',(W/'CLAUDE.md').read_bytes(),str(W/'CLAUDE.md'),'First75 lines directly read; entire local raw file retained as context',None)
]
for name,raw,source,scope,pin in sources:
    if pin is not None:need(digest(raw)==pin,'Source pin mismatch: '+name)
need((W/rel).read_bytes()==sources[0][1],'Working proof differs from frozen Git source')
blob=subprocess.run(['git','-C',str(W),'rev-parse',commit+':'+rel],capture_output=True,check=True).stdout.decode().strip()
need(not D.exists(),'Audit output already exists; no overwrite')
(D/'subjects').mkdir(parents=True)
subjects=[]
for name,raw,source,scope,pin in sources:
    (D/'subjects'/name).write_bytes(raw)
    subjects.append({'path':'subjects/'+name,'bytes':len(raw),'sha256_raw':digest(raw),'source':source,'read_scope':scope,'representation':'Exact raw bytes; no normalization'})
prompt="""Mandatory separate exact-source audit under repo OPERATIONAL-GOVERNANCE-CHARTER.md §4. Audit frozen commit2f370a7da850b8066a9afe95c523e49bd1ef725e at C:\\Trabajo\\the-eriksson-programme\\perron-spec-210-20261108; papers/flat-coarse-rank/research-consolidation/coarse-window259/coarse-window-obstruction259A.txt raw SHA25603c71a1a4a652a6d28bc38acc43b7a2227796a300d673e1611f65417bb50557f. Adversarially verify whole theorem, particularly tagged multiset windows (K>=n, repeated positions, cyclic seams, no global labels), (K-1)q unchanged+q moved slots, sharper K|u|²+2|u|S+S² translation estimate, finite convolution radii and original source weights, actual real coexact membership/means/nonzero bound, every constant, contraposition for all K, and explicit n=2^m,kappa=n/4+2,q4,K4,S8,A148 rapid-grid counterexample incl B*=kappa/gcd claims. Freshly verify imported257A cutoff lemma at fed201fd10f952a04e638c324dc0e1359711911a raw8b92c1aeae67c26832cdd4e53dfcfb62537640d3d2a0a96370e677c3cd1ddbbc; source258A at d7840f33a5e20120565f3d5803dfabb32802de95 raw0c99070cdea4a3c7edf7168a8dfd2eb6eca96b08ed21e5002c003424ee7d66dc, no inherited verdict. Preserve full objections/failed estimates. Read-only source/branch; no commit, PR, runtime, numerical/mathematical script, Lean/compile, desktop/browser UI or other-chat/automation action. Reasoning/file/git/hashes only. Capture all directly read mathematical/governance subjects and full original report/prompt/context/raw hashes in D:\\Datos\\the-eriksson-programme\\autonomia\\evidencia-259\\source-audit259A. No score/grade/formal/numerical/peer review or independence claim: same involved Codex/OpenAI GPT6family, exactbackend/version/effort unavailable; inheritedparentcontext disclosed. PR/body nonexistent at assignment, captureN/A. I will send no inbound messages while audit runs. No disposable clone needed; all acceptance checks explicit, no Pythonasserts. Return verdict, fullreport/manifest rawhashes, subject/file count and proofblob.
"""
report="""259A EXACT-SOURCE ANALYTICAL AUDIT — COMPLETE ORIGINAL REPORT
11November2026

VERDICT: ACCEPT_ANALYTICAL_COARSE_TIME_WINDOW_OBSTRUCTION_AND_STATED_RAPID_GRID_COUNTEREXAMPLE_WITH_LIMITS.
Exact frozen source commit: 2f370a7da850b8066a9afe95c523e49bd1ef725e.
Proof raw-byte SHA256: 03c71a1a4a652a6d28bc38acc43b7a2227796a300d673e1611f65417bb50557f.
No blocking mathematical defect found. A nonblocking wording clarification
about the designated unchanged-slot count is retained below; the derived
translation estimate and theorem do not depend on an exclusive zero count.

METHOD AND EXACT INPUTS
I read all of259A and both named frozen257A/258A mathematical sources.
I freshly checked the257 single-corner cutoff and rederived the259 tagged
matching, exact-image/observation, commutator, norm, source-energy, all-K
contraposition and explicit fast-grid claims. No previous verdict is a proof
input. The entire governance charter and the first75 CLAUDE lines were read;
full raw context files are captured with their actual read scopes.
Only analytical reasoning, file reads/copies, byte hashes and Git identity
reads were used. No numerical enumeration, mathematical script, Lean/Lake,
oracle, symbolic engine or Colab runtime was run. Hash checks establish
provenance, not mathematical or formal certification. No PR/body existed in
the assignment; body capture and normalized-body hash are N/A.

1. SINGLE-CORNER CUTOFF — ACCEPT AFTER FRESH CHECK
With R=n/4>=8 and L=log((R+1)/3), the clipped logarithm vanishes at radius<=2
and is1 at radius>=R. Only square-boundary crossings r to r+1 for2<=r<R
contribute. There are8r+4<=32r such forward-counted edges and increments
<=1/((r+1)L). The chart lies within n/4, avoiding antipodal distance seams.
The harmonic bound gives32log(R+1)/L^2<=64/L, since R>=8 implies
log(R+1)<=2L. For the deficit, the stated dyadic bins have at most
4(R+1)^2/4^k sites and deficit<=(k+1)log2/L. The clipped inner plateau is
covered because its unclipped deficit is at least1. The series is80/27<4;
therefore the squared deficit is<=16(R+1)^2/L^2<=4n^2/L^2. Translation and
bin/plateau endpoints do not introduce an uncounted seam or multiplicity.
The imported bounds are valid without an external sharp capacity theorem.

2. ORIGINAL ACTUAL COEXACT DOMAIN AND MEANS — ACCEPT
For forward curl23=partial2u3-partial3u2, its adjoint components are
delta3psi23 and -delta2psi23. With psi23=delta2delta3Psi this is exactly
P Psi=(0,delta2delta3^2Psi,-delta2^2delta3Psi). It is a real periodic
preimage in the actual image, not merely a divergence-free surrogate.
Complete component sums vanish by a periodic first difference.
At each fixed i, applying cyclic-interval telescoping in both coordinates
reduces cell sums to four-corner differences of delta3Psi or -delta2Psi.
Starting-endpoint-minus-one values are predecessor terminal endpoints;
wrapping cells obey the same identity and a whole-cycle factor cancels.
The original E_i therefore suffices. Making eta vanish at each corner and
its backward transverse neighbors makes both required Psi differences zero.
No new observations on the auxiliary cover replace the original mean map.

3. TAGGED WINDOW BIJECTION — ACCEPT, INCLUDING K>=n
F_i has one distinct TAG for every pair(j,p),0<=j<K,p in E_(i+j), even
when several pairs share a spatial point or i+j repeats modulo n.
For each j>=1 the target tag j-1 in F_(i+1) has exactly the same spatial
set E_(i+j), so identity matching is bijective on that entire q-entry block.
These cover target tags0,...,K-2. The outgoing tag0 block E_i is mapped
bijectively to E_(i+K) at target tag K-1 by the given K-step matching.
The domains and target tag blocks are disjoint, so their union is a genuine
bijection of Kq entries. This proves the construction even for K>=n,
repeated spatial points, the i=n-1 seam and nontrivial label permutations.
It never requires global labels or concatenating K-step matchings.

Nonblocking wording clarification N1: the source's phrase 'Exactly(K-1)q
entries are matched with zero displacement, q with displacement<=S' counts
the DESIGNATED shared block and the q replaced slots. The replacement
matching may also contain zero-displacement pairs, particularly when S=0.
Thus the total number of zero-displacement pairs can exceed(K-1)q. If read
as an exhaustive total-zero count, 'exactly' would be too strong; 'at least'
is the unambiguous total-count wording. The proof uses only the correct
designated-block bounds, not an assertion that the replaced slots move
strictly positively. This is not a defect in(2) or the theorem and requires
no changed constant. Preserve this clarification with the frozen source.

4. MINIMUM AND SHARED-WINDOW TRANSLATION COUNT — ACCEPT
For finite equally indexed real lists, min is1-Lipschitz in the maximum
norm. Squaring and bounding max by sum is valid with repeated list entries.
Each of the designated(K-1)q shared entries has center displacement0 and
cutoff-shift norm<=|u|_1 sqrt(64/L). Each replaced slot has center
displacement<=S, costing at most(|u|_1+S)sqrt(64/L). Therefore the squared
minimum difference at a slice is at most
(64q/L)[(K-1)|u|_1^2+(|u|_1+S)^2]
=(64q/L)[K|u|_1^2+2|u|_1 S+S^2].
This correctly avoids multiplying the S^2 term by K. For longitudinal shift0
identity matching of all Kq entries instead gives64Kq|u|_1^2/L. Summing
the slice bounds gives their full-X factor n. Only longitudinal shifts0,+1
are used later. The cutoff deficit is the maximum of Kq nonnegative
individual deficits, yielding4KqV/L^2. No smoothness or derivative of a
minimum is assumed. The cover includes E_i exactly as needed for the means.

5. LOW WAVE AND ORIGINAL SOURCE PARITY — ACCEPT
The identities delta sin=sin+cos and delta2delta3sin=2cos give the stated
w=(2,-2,-2,2) for the third difference. Thus z0=(0,w,-w) has pointwise
squared norm8, full squared norm8V and comes from the actual potential.
At odd total residues1 and3, advancing any coordinate preserves w:
w(2)=w(1) and w(0)=w(3). All original odd-source forward differences of
z0 are zero. Divisibility4|n handles the phase seam. The phase is correctly
left in the original coordinates instead of transported with the window.

6. FINITE CONVOLUTION RADII AND CONSTANTS — ACCEPT
The commutator identity is exact term by term; shifted Psi0 is bounded by1.
Each of P's two nonzero components has coefficient l1 sum<=8, transverse
radius<=3 and no longitudinal shift. The shift0 bound therefore gives
2*(8*3)^2*64nKq/L=73728nKq/L for the squared norm commutator.
For partial2P and partial3P, the l1 sum is<=16, longitudinal shift0,
transverse radius<=4, so the squared-radius cost is<=16K. For partial1P,
the only longitudinal shifts are0,+1, transverse radius<=3 and l1 sum<=16.
The +1 cost is<=9K+6S+S^2; the shift0 cost is<=9K. Consequently A bounds
every term's squared-radius cost. Applying the l2 triangle inequality first
gives each derivative commutator norm<=16sqrt(64nqA/L), regardless of
coefficient cancellations or repeated translations. Six squared bounds
sum to98304nqA/L. Restricting to original odd sources is legitimate because
eta partial_h z0 vanishes there. H remains attached to the original source,
not a shifted target; eta is not silently treated as x1-independent.

7. NONZERO WITNESS AND FINAL ENERGY — ACCEPT
The split into(eta-1)z0 and the P commutator, followed by the two-term
squared-norm inequality, gives16||1-eta||^2+147456nKq/L. With the deficit
bound and n<=V this is at most(64Kq/L^2+147456Kq/L)V.
A>=16K makes the threshold imply L>=2^22Kq, so the coefficient is at most
2^-38+9/256<2, as Kq>=1. Reverse triangle proves ||z1||>sqrt(2V), not
just that its potential is nonzero. Multiplying the strong sum by H=cn^2
gives98304cVqA/L<=3cV/8 because98304/2^18=3/8. The strict norm bound
makes this<3c||z1||^2/16. The full unweighted three-direction energy is
<=12||z1||^2, so the weak-source sum is<=12a||z1||^2=c||z1||^2/4.
The total is strictly less than7c||z||^2/16, stronger than the displayed
weak inequality. All original means vanish and channel2 is zero, hence
every quadratic form of that observation vector vanishes. The result is
in the actual original domain and norm, without a projection/gap assumption.

8. RAPID HELICAL APPLICATION AND ALL-K CONTRAPOSITION — ACCEPT
For n=2^m,m>=5 and kappa=n/4+2, both singleton complements are nonempty
cyclic intervals. Their terminal endpoints give
E_i={t_i,t_i-1}x{0,n-1}, q=4. The identity4kappa=n+8 proves the required
K=4 matching with S=8, including every time seam. Then A=max(64,148)=148
and the threshold is2^18*4*148=2^20*148. Arbitrarily large powers of2 have
L above this finite threshold, so the claimed24n-row failure is nonvacuous,
though far outside a practical crossover claim.
For adjacent motion, kappa<n/2-1. The new point with x2=t_i+kappa is at
distance kappa from t_i and at the larger distance kappa+1 from t_i-1;
neither periodic wrap nor adding x3 displacement reduces that lower bound.
Translation matching attains kappa for all points, so B_*=kappa exactly.
Also kappa=2(2^(m-3)+1) has precisely one factor2, hence gcd(kappa,n)=2
and the singleton orbit contains n/2 positions. Thus this is genuinely a
large-one-step-motion family; its short coarse-time resonance still defeats
recovery. Large one-step B is a necessary escape condition from258, not a
sufficient recovery condition, so there is no contradiction with258A.
For each K, finite equal-cardinality sets attain their bottleneck S_K.
Applying the theorem with S=S_K and contraposition proves(6) for every K.
Different K may give different witnesses; necessity does not require a
common witness. No converse or general canonical optimum follows.

OPEN LIMITATIONS AND OBJECTIONS
O1. GlobalQ251 remains OPEN. The result retains constant q product slices;
variable q, general nonproduct/canonical maps and motion without an effective
short matching resonance are not settled. It is not unconditional removal
of all geometric hypotheses or a global nlogn theorem.
O2. Priority/originality of this exact application is UNESTABLISHED. Capacity,
minimum, translation and shared-window ideas are classical. No primary-source
equivalence audit or importance assessment was performed by this session.
O3. The constants and finite threshold are enormous and unoptimized. No
numerical implementation, experiment, practical crossover or benchmark was
checked. The finite coexact counting model is not a physical spectral gap
or a continuum construction; PR29 and TermSource are unchanged.
O4. This is a separate involved Codex source-audit session with inherited
parent conversation and construction visible. Blindness and model/provider/
statistical independence are not established. Available identity is
Codex/OpenAI GPT-6 family; exact served backend/version/effort are unexposed.
No score, stars, PDF review, formal verification, numerical certificate,
human peer review, editorial acceptance or new publication is supplied.
O5. Retain N1, the zero-displacement wording clarification, with this exact
frozen source. It does not alter the mathematically used shared/replaced
slot count, estimates or conclusion. No failed mathematical gate was amended.

OPERATIONAL BOUNDARY
No inbound parent messages or partial results arrived while auditing.
No proof/branch, other chat or automation was modified. No runtime, clone,
worktree, PR or desktop/browser control was created or used. Cleanup is N/A.
The full original assignment and declared model/review context are separate
files. Full inherited account conversation is not exportable by a tool; its
visibility is disclosed, not a fictitious complete transcript claimed.
Raw source and context captures identify their byte representation without
normalization. The output seal is file/hash provenance work, not a mathematical
script or source of any analytical inequality above.
"""
verdict='ACCEPT_ANALYTICAL_COARSE_TIME_WINDOW_OBSTRUCTION_AND_STATED_RAPID_GRID_COUNTEREXAMPLE_WITH_LIMITS'
context={'recorded_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'task':'/root/coarse_window259_source_audit','verdict':verdict,'exact_commit':commit,'proof_sha256_raw':sources[0][4],'proof_git_blob':blob,'model_identity_exposed':'Codex/OpenAI GPT-6 family; exact served backend/version/effort not exposed','independence':'Separate child session of same involved programme; inherited parent conversation and construction visible; not blind or independently established','formal_verification':False,'numerical_experiment':False,'numerical_grade':None,'external_novelty_audit':False,'inbound_parent_messages_during_audit':False,'PR_body_capture':'N/A: no PR/body existed in assignment','PR_normalized_body_hash':None,'runtime_created':False,'disposable_clone_created':False,'source_or_branch_modified':False,'subject_count':len(subjects),'subjects':subjects,'nonblocking_clarification':'N1: designated(K-1)q shared slots have zero displacement; replaced slots may also have zero displacement, so total zero-displacement count need not equal(K-1)q. Bounds and theorem unchanged.','context_export_limit':'Complete assignment captured; full inherited account conversation is not exportable by a tool; its visibility and limits are explicitly disclosed.'}
(D/'prompt.txt').write_text(prompt,encoding='utf-8')
(D/'full-report.txt').write_text(report,encoding='utf-8')
(D/'review-context.json').write_text(json.dumps(context,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
shutil.copyfile(__file__,D/pathlib.Path(__file__).name)
files=[{'path':p.relative_to(D).as_posix(),'bytes':p.stat().st_size,'sha256_raw':digest(p.read_bytes())} for p in sorted(D.rglob('*')) if p.is_file()]
manifest={'representation':'Exact raw bytes; no normalization; manifest excludes itself','verdict':verdict,'source_commit':commit,'source_sha256_raw':sources[0][4],'source_git_blob':blob,'subject_count':len(subjects),'subjects':subjects,'files':files}
(D/'hashes.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
for v in files:
    p=D/v['path'];need(p.stat().st_size==v['bytes'] and digest(p.read_bytes())==v['sha256_raw'],'Output seal mismatch')
need(gitraw(commit+':'+rel)==sources[0][1] and (W/rel).read_bytes()==sources[0][1],'Source changed during audit')
print(json.dumps({'verdict':verdict,'report':str(D/'full-report.txt'),'report_sha256_raw':digest((D/'full-report.txt').read_bytes()),'manifest_sha256_raw':digest((D/'hashes.json').read_bytes()),'subject_count':len(subjects),'manifested_files':len(files),'proof_git_blob':blob,'nonblocking_clarification':'N1 retained in full report/context'}))
