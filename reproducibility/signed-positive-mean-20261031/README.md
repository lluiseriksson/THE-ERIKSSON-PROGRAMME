# Actual signed weights controlled by positive spatial parts

Exact proof source 810785b17b2f1bb14dd6caa5435865eb51a86ef3 passed two fresh own Colab Linux clones077/077b.
All nine stages and six exact standard-axiom reports passed; compiled target,
raw oracle and LF-source-manifest hashes match. Real oracle mutations3 rejected
and positive1 accepted in normal and optimized Python. See actual reports.

signedWeightPositivePart is the actual pointwise function max(w(p),0).
Nonnegativity and actual energy monotonicity are proved from the weighted
gradient sum, then local divergence-free coercivity is transferred upward
without changing C,L,Phi,c,K,delta,radius. The finite bound and actual-family
output finrank divergence use the constructed positive-part spatial mean.
There is no lower bound on original signed weights, no original-operator
positivity assumption, and no supplied band/trace/order certificate.

Retained: fixed d,Nc and distinct i,j, Nc>=2, fixed c>0, zero observation and
Frechet derivative at zero, original locally upper-quadratic penalty and
local divergence-free coercivity. Output spaces and K/delta/radius may vary.
This changes the explicit mean hypothesis for signed weights: mean(max(w,0))
is not max(mean(w),0). It does not prove original weights nonnegative or an
interacting/continuum/density theorem. PR29 remains20/41,TermSource=0.

The complete ordinary-signed-mean counterexample from unit056 remains an
ANALYTIC proof, not a new Lean endpoint in this module. All ordinary means
can vanish while fixed output and quadratic penalties give global coercivity;
its positive-part means instead grow quadratically, so there is no conflict.

Both own CPU/highRAM runtimes released and own notebook tabs closed; interval
scope is recorded, not billed units. No Windows Lean/Lake/oracle, GPU, external
model or independent scientific review. Pinned Mathlib cache used, not a full
Mathlib-from-source audit. The unexecuted a95b615a numeric driver-label change
was corrected to retain Mathlib076427... before execution, with source and
six-endpoint acceptance criteria unchanged. It was not a failed compilation.

Classical energy order and existing actual trace/rank mechanisms; no general
original-priority claim. Full raw evidence remains preserved in D and compact
reports/logs here. The exact authorized15page e5e9 v4 PDF remains unchanged,
contains neither later signed result, and awaits the existing author workflow
when the already requested Netcup login is ready. No duplicate approval,
new paper/PDF/deposit/license/publication or inherited assessment is claimed.