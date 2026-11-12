# Unit277 fabrication: six fixed finite diagnostics

This is implementation and construction documentation for a **separate reviewer**.
It is not an audit, executed result, rank certificate, theorem, novelty finding or
physical-gap claim. No numerical code has run on Windows or Colab in this task.
The parent owns mathematical/engineering review, the final commit and execution.

The primary diagnostic selected for review/execution is `diagnostic277B.py`, raw
SHA256 `256362a3d76b4c3609d3bba9f58966ddf05776f27f1789f6a151ada99735ada5`.
Original A (`diagnostic277.py`, raw
`ba9f495125acad9f6ddd12d64564f7e966324ebc52eb8677dc4ee75427f3d984`)
is preserved exactly. A parent freeze message overlapped the final B edits. A was
restored to its exact original bytes; B is a separate file, preferred by parent.
The full A-to-B delta is retained. B adds finite eigensolver-output checks,
reduced eigen-equation residual, and retention of actual arrays/residuals/alternate
rows before integrity failures; it changes no mathematical assembly or parameters.
Neither A nor B will be edited further; a necessary correction needs a new version.

## Fixed question and domain

Read `layer-stream275A.txt`, `constraints276A.txt` and mandatory `STATUS276.txt`
together. The old tau=0 redundancy sentence is false: retain singleton AND total.
The implementation builds actual nonempty original cells, so drops no endpoint
total. It does not use the quantitatively excluded whole-plane-zero shortcut.

For each odd s and y=(y1,y2), physical paired sites are
A_s(y)=(y1,y2,s-y1-y2), B_s(y)=A_s(y)+e3 modulo n. Channel1 values at both sites
equal V_s=t_s+(delta2 psi_s,-delta1 psi_s,delta1 psi_s-delta2 psi_s), channel2zero.
Every delta is backward I-shift(-e_j). Fix psi_s(0,0)=0. For each odd s except
the last, the two constant parameter columns give (1,0,-1),(0,1,-1) on that
layer and their negatives on the last layer. Thus sum_s t_s=0 and spatial sum0.
There is no additional implicit restriction on potentials. This parametrizes
the exact275 class, not all actual coexact fields.

The fixed dimension is (n/2)(n²-1)+2(n/2-1)=n³/2+n/2-2:
32 at n4,258 at n8,2054 at n16. Parameter order: increasing odd s, increasing
lexicographic y excluding(0,0), then the two transverse constants per nonlast s.
Physical order is x1,x2,x3,component with component last. Layer alternative order
is s,component,y1,y2. c=1,H=n² on odd physical SOURCES,a=1/48 on even SOURCES.

The six cases are exactly n=4,8,16 crossed with tau_i=2i² modn and tau_i=0.
No additional sizes/cuts, adaptation, threshold hunting, acceptance counters or
data-dependent cutoff choices. This is classical exploratory selected finite data.

## Two independent assembly formulations

Physical B is a sparse point-stencil scatter for every potential and constant
parameter to paired physical sites. Physical G=B^TB uses counting norm. Physical
K sums every forward direction/component through sparse weighted differences of
B rows. No dense (3n³)² physical Laplacian is ever allocated.

The alternative layer T is built separately from sparse backward delta matrices
and gauge embedding, then layer/component block operators. It computes G_alt=2T^TT;
Q_H=H sum_s,y,j=1,2 |V_s(y+e_j)-V_s(y)|²; Q_a=a sum_s,y,j=1,2,3
|V_(s+2)(y+e_j)-V_s(y)|², interpreting j3 as no transverse shift. This is275(2),
including layer wrap and exact paired norm factor2. Full sparse K/G comparisons
and symmetry discrepancies are reported at tolerance1e-8 scaled by maximum entry.

C contains every original nonwrapping slice cell, all components and both
channels, with coefficient1/sqrt(n³|cell|). Channel2 rows are explicit zero rows
because this class has channel2zero. Empty intervals alone are omitted. The
independent row assembly uses276: E_i(j)=V_sigma(i+j)(i,j), W_i(j)=sum_s V_s(i,j),
short sums E and long sums2W-E, retaining original normalization for EACH actual
row. R=CB is compared to R_alt=C_layer T. No cyclic union or reduced unnormalized
row replaces the original observation map in the eigenproblem.

## Numerical reduction and output

Full real SVD uses scipy.linalg.svd, drivergesvd, full right basis. Rank is number
of singular values STRICTLY above1e-10 times largest singular value. All returned
singular values, actual absolute cutoff/rank/nullity and fixed relative cutoff
are recorded. Z is the numerical right null basis. This is not an exact rank
certificate. If nullity0, record an explicit empty numerical-kernel result and
empty parameter-vector file; minimum/witness are null, never a fabricated vector.

Otherwise solve the smallest generalized eigenvalue of Z^TKZ against Z^TGZ with
scipy.linalg.eigh(gvx), using the physical Gram; not an ordinary Euclidean
parameter eigenproblem. Fix sign by largest-magnitude parameter and normalize
actual physical field to counting norm1. Record full parameter eigenvector,
null-coordinate eigenvector, actual physical field, actual observed rows and
explicit real/FFT curl-adjoint preimages. Matrix B/K/G and original R are saved
as sparse NPZ. This is a selected finite computed candidate, not an asymptotic
construction or a lower bound for full U. Degenerate eigenvectors may differ
across numerical libraries despite deterministic assembly/sign convention.

Recompute physical Q_H,Q_a,Q and norm from all physical forward labels. Check
original rows again by independent direct cell loops, backward divergence,
global mean and275 energy/norm formulas. Explicit orthonormal 3D FFT uses
g_j=exp(2pi ik_j/n)-1 and Ahat_jl=(g_j uhat_l-g_l uhat_j)/|g|² for k!=0;
Ahat(0)=0. Reconstruct actual counting curl adjoint in physical space from real
inverse-FFT A, retaining imaginary residue. All listed residuals must be finite
and<=1e-8 after their reported scale; reduced generalized eigen-equation and
physical Rayleigh/eigensolver agreement checked too. These are floating numerical
integrity checks, not coexactness/rank/formal certificates. Failures retain actual
case JSON, traceback and existing source arrays/residuals; no trial is rerun.

Case failures do not suppress later fixed cases. Model-construction failure stops
that run with failure report. Empty kernel is an explicit diagnostic result.
NumPy/SciPy/Python versions and raw executed script hash recorded. BLAS environment
thread counts set1 before importing NumPy/SciPy in the standalone child. No seed
or random search is used. K/G stay sparse until nullspace reduction; only parameter
SVD/reduced matrices are dense. n16 B is sparse, d2054; dense reduced/SVD working
arrays have O(d²) storage. Exact peak RAM/wall-time is NOT measured or promised;
CPU/high-memory runtime is prescribed and n16 is a hard cap.

## Disconnected owned wrapper

RUNNER-HASHES covers diagnostic277B.py,launch277.py,capture_cli_atomic.ps1,
run_owned_after_gate.ps1,readback_after_stop.ps1. Capture helper is copied from
retained274B. Bootstrap is the bounded proven standalone pattern after the actual
notebook-argv/CLI0 incident. It embeds exact B bytes/raw hash, writes/fsyncs/closes/
reads back `/content/tep277-launch/launch/diagnostic277B.py`, **outside** the fresh
diagnostic root, and starts `[sys.executable,path]`. It reads neither kernel argv
nor notebook __file__. No diagnostic guard is weakened for notebook execution.

Parent's outer wrapper requires exact final manifest/source hash, actual parent
full separate mathematical/engineering report reads/acceptance and report hashes
through D:evidencia-277/parent-authority-relay.json. `-SourceSha` is the actual
future parent-frozen commit, saved in outer report/relay; diagnostic child records
actual raw source hash and accepted construction base801004. There is no runtime
Git clone or falsely claimed runtime Git HEAD. Parent must verify committed B raw
bytes equal the relayed hash. This single exploratory run is not terminal
two-clone reproduction.

Unique own CPU/high-memory sessiontep277-diagnostic-own-cpu, unique config
tep277-diagnostic-sessions.json. Bootstrap `/content/tep277-launch` is disjoint
from `/content/tep277-diagnostic`. Native results ZIP and envelope are unique;
outer downloads to D:evidencia-277/attempt-a, then finally stops only its own
runtime and requires separate literal inactive-backend readback. Existing attempts
refused. Real child stdout/stderr/actual closed decimal exit and receipt retained,
not providerCLI0 alone. Envelopes include native ZIP even failed if present, or
actual partial evidence otherwise. Parent must audit complete raw membership and
logs after execution; preliminary transport is never mathematical acceptance.

Standalone timeout3300s and outer3600s leave finite capture time; slow work/platform
loss can still interrupt evidence. Direct-child kill may leave descendants until
whole own-runtime stop. Billing units remain unknown; wall time is not billed
units. Runtime package availability, numerical conditioning, Gram positivity,
cutoff sensitivity and LAPACK variation remain limitations. No execution occurred
here, and no result, witness belowc, counterexample, full-U coercivity, priority,
physical gap, continuum theorem or new paper is asserted.

## Role/context

FABRICATOR only. Parent and a DIFFERENT auditor must review actual exact B/source
and wrapper before allocation. This document is construction notes, not a self-
audit/acceptance. Exposed identity Codex/OpenAI family; exact served backend/
version/effort unavailable, shared inherited programme context, no independence
claim. No source/runner from prior units, existing untracked helpers, state,
other chats/agents or automations changed. No commit/push/runtime/math run by me.
Raw source package is preserved under D:evidencia-277/source-preparation.
