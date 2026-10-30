# Concrete local derivative repairs with no rank bound

The selected realization of the local-gradient question uses the repository's
actual flat curl D and divergence Q, with multiplication by real spatially
varying weights W and Z. The fine operator is constructed as

    V = D* W D + Q* Z Q.

Both multipliers and the adjoint compositions are defined, rather than supplied
as an assumed quadratic-form inequality. On the actual physical counting L2
space the proved multiplier form is sum_i w_i*norm(x_i)^2. Consequently

    <A,V A> = sum_p w_p*norm((D A)_p)^2
              + sum_x v_x*norm((Q A)_x)^2.

If weights are nonnegative this form is nonnegative. If both weight fields
are bounded above by one M, then for every actual physical A,

    <A,V A> <= M*<A,K0 A>.

No rank, translation-invariance, smoothness or comparison-subspace assumption
is made on V. The nonnegativity hypothesis is needed only for the separate
positive-form result; the upper bound and obstruction even allow negative
weights bounded above. Unit weights reproduce the flat K0 quadratic form
exactly. No new formal rank formula or operator equality is claimed merely
from that energy identity.

For the constructed real Fourier band, dim2B=2*(2R+1)^d and2R<n, the energy
of K0+V is therefore bounded above by

    (1+M)*4*pi^2*d*R^2/n^2 * norm(A)^2.

Any linear measurement C into a finite real F and any finite-valued Phi with
Phi(0)=0 fail to establish a full-space lower bound with c above that threshold
when dimF<2B. Only kerC is needed: there is no intersection with kerV and no
uniform rank budget. For a family n_L=(L+1)Nprime, fixed finite F, weights
uniformly bounded by one fixed nonnegative M, and arbitrary C_L and Phi_L,
there is no positive c chosen before every L for the full-space estimate.
The proof chooses R=dimF+1 and then chooses L with lambda<c/(1+M), using the
already proved Archimedean refinement lemma and actual physical band.

This is a different sufficient obstruction class from the earlier theorem for
arbitrary repairs of uniformly bounded rank. It does not prove the earlier
rank condition redundant for arbitrary operators. The coefficient bound and
derivative form are explicit assumptions of the new model class, not a physical
Hessian estimate that has been proved or smuggled into a new structure.
The current concrete family weights curl/divergence outputs. The original
componentwise sum_i w_i(x)*norm(forwardDifference_i A(x))² is a related family;
its exact CLM construction and transport are not silently claimed here.

Locality by itself would be insufficient. The radius-zero repair V=identity
is an analytic counterexample to that overstatement: since K0 is nonnegative,
<A,K0 A>+<A,A> >= norm(A)^2 at every size, with zero measurement. A zeroth-order
mass term is outside the derivative-form family above. Coefficients growing
like L², a physically scaled L²K0, a growing observation space or a different
physical operator also require separate analysis. No Yang--Mills mass gap,
continuum limit, Wilson-Hessian identification, hRpoly producer or PR29 change.

## Originality and relevance

Weighted derivative-energy comparisons are classical. Spielman's primary survey,
Graphs, Vectors, and Matrices, section2, explicitly defines the weighted graph
Laplacian by a sum of weights times squared differences:
https://cs-www.cs.yale.edu/homes/spielman/PAPERS/bull1557.pdf .
It supports the classical background, not a claim that the survey contains this
repository's cochain normalization or theorem. Here the comparison follows
from the displayed finite sum, followed by the already constructed Hodge band.
No new general spectral principle or exhaustive priority audit is claimed.
The programme relevance is a checked concrete derivative-repair obstruction
without a rank bound. It belongs with the existing flat-kernel dossier; it is
not a new small paper or an update of the frozen eight-page PDF.

## Model assessments and review context

Prepared by the same Codex agent with prior programme context. No independent
scientific reviewer, exact served alternate model identity, numerical score,
peer review, acceptance or publication is attributed. Focal compiler/oracle
checks and fresh clones test formal validity/reproducibility, not originality
or independent scientific assessment. The frozen eight-page manuscript and its
review packet remain unchanged while this separate code unit is tested.

## Verification

Source acf33d4fc9d9d98efe4d7df2c068cb9a6f7972d4 passed two complete fresh
serial Colab clones035/035b. Each recovered ZIP was validated for12manifest
entries,2source files,9exit-zero steps and8exact named oracle reports, all
using exactly propext,Classical.choice,Quot.sound. Actual-log positive acceptance
and rejection of3real-field mutations passed under normal and optimized(-O)
Python; no acceptance uses assert. Start times and bundle hashes differ while
source, .olean, oracle.log and source-manifest hashes match.

| Artifact | SHA256 |
| --- | --- |
| ZIP035 | 802eec785d1baa60791362d6bc411986f90626c9614451b304215f5d46e8d556 |
| ZIP035b | 1aa816ecc6933db27db4109f29ed69cdaf10ea36b0b0f4948dcfebb8544a0d30 |
| .olean both | c705b57bef8865c5d749b3b6d04628634b5213cacd6373435388e6156dc76a3a |
| oracle.log both | 9fbe4d99a8a25cc22c93e65edacf638fec95bde392332a261be7e98542fb8979 |
| source-hashes.json both | 3e9f7f2be5ddd120da76f44a8d47e21be02bdaed540b7fa99f38bc60ef5408b5 |

LF source hashes: module7d9bc74da9f7b302193f5633fd2eb9aecce383f7c4aff10c8a3a578c1258ac5d;
oracle47f0b2cba7ed5f4f3ae93577660e89fca36829c66ec5b44be46552e7c46b295f.
The repository convenience driver only trims EOF blank lines; exact input
notebook and original driver are retained. Scoped heartbeat allowances are
resource settings, not theorem hypotheses or changes of the judge.

Failures033 atf3efa4aa and034 at54662efa are retained in full, including
manifest-verified failure reports and exact input notebooks/hash pins. Both
failed to simplify the zero auxiliary map's range dimension in the original
proof attempt. The final proof uses the direct injectivity/kernel argument
for C restricted to the actual band. No statement, acceptance rule or oracle
criterion was weakened. No local compilation was used.

Four serial CPU/high-RAM runtimes, all automatically released and disconnected
UI checked: failed033284.056581s; failed034327.588365s; pass035211.701654s;
pass035b391.379138s. Total1214.725738s reported driver execution. Allocation
overhead and compute units were not measured; no GPU or additional charge.
Full raw UTC intervals, outputs and validation records are preserved in the
reproducibility/weighted-flat-repair-20261030 directory.
