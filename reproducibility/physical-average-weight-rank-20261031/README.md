# Actual finite physical average-weight rank inequality

Verified proof source d03ab7ef930a2ad9de6346803bad30c395e9bfc9. For Nc>=2, distinct transverse directions i,j,
R<n, nonnegative actual componentwise repair weights and actual local
divergence-free nonlinear coercivity with c>=0, C(0)=0, Frechet derivative
at zero and a locally upper-quadratic penalty, the theorem derives

    c*(2R-dim_R F) <= 2*(1+b_ij)*sum_(r=1..R) |stdAddChar(r)-1|^2,
    b_ij = n^(-d)*sum_x w(i,(x,j)).

This is the actual finite flat unit-spacing physical cochain operator, not
an abstract supplied low band. The local derivative-kernel lower bound is
derived by the Frechet norm-ratio limit, small scalar directions and an
explicit positive normalization. Actual strip divergence is derived by
span containment in the actual constraint kernel. Actual positivity comes
from the Hodge and nonnegative G*WG operator lemmas. An actual orthonormal
basis is constructed via Basis.span; the inclusion-adjoint compression trace
is identified with the exact normalized-family energy sum. Unit051's proved
positive compressed trace/rank inequality is composed with these results.

The final endpoint assumes no pointwise cap or supplied band dimension,
orthonormality, kernel coercivity, positivity or trace certificate. It does
retain nonnegative weights and the original upper-quadratic penalty. This
is not a universal extension over signed weights covered by some older
pointwise-cap theorems. K, delta and radius can depend on the finite lattice;
no n-uniformity of those constants is used here.

Two fresh own Colab Linux clones 075/075b of the SAME source passed
six exact standard-axiom reports, all execution stages and actual mutation
rejection3/positive1 in normal/Python-O. Compiled target, raw oracle and LF
source-manifest hashes match. Pinned Mathlib cache used, not a full Mathlib
source rebuild. No Windows Lean/Lake/oracle or GPU. All own runtimes released
and notebook tabs closed; raw reports and disconnected captures retained.
All failures, original sources and exact patches are preserved; prepared b
drivers corresponding to failed first attempts were not executed.

The finite physical inequality is formal. The quantitative multiplier bound
and asymptotic output-rank divergence for (1+b_ij(n))/n^2 ->0 remain to be
formally composed. This is not a volume-density lower bound. No interacting
or continuum Yang-Mills hypothesis is removed and no physical mass gap is
claimed. Unit050's penalty counterexamples are retained. PR29 remains20/41,
TermSource=0. Frozen public AIRR v3 unchanged; no new PDF/paper/deposit/licence
or model assessment. Classical methods and pinned primary sources, without
original-priority or independent-review claim. Keep the grouped dossier.