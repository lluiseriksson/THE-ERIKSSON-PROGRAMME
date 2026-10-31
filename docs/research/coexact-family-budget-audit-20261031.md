# Preparing-agent derivation audit — no independent review

Artifact: coexact-family-budget-20261031.md, same directory. This is a manual
mathematical check, not a test run, external model report or Lean certification.
The audit covers a single analytic route and records its limits.

1. Actual operator dictionary inspected at base6b7f5cf:
   PhysicalGaugeCochains.lean defines SUNLieCoord as EuclideanSpace over
   Fin(Nc^2-1), physical one-cochains as counting-L2 bond fields,
   gaugeConstraintQCLM as covariant divergence, and proves
   gaugeConstraintQCLM_trivial_apply as the actual backward divergence.
   flatGaugeHodgeK0CLM is the actual trivial-background Hodge operator;
   its underlying definition is the sum of adjoint products, hence
   selfadjoint. The global componentwise-gradient identity was already
   proved, not introduced as a hypothesis in this note.
2. Fixed-output subquadratic contradiction checked a second way with a
   fixed integer R and the exact tested finite theorem. It avoids spectral
   completeness, floor arithmetic and the proposed sharp multiplicity count.
   Thus that conclusion does not inherit the extra analytic obligations of
   the sharp classification.
3. Floor route checked at its smallest allowed alpha*n=2: R=2, not0;
   floor(t)>=t/2 for t>=2. Since alpha<=1/4, 2R<=n/2<n for positive n.
   Threshold<=c/4 leaves a strict margin; no equality case is silently used.
4. Tangent argument: derivative kernel gives C(tv)=o(t), not exact C(tv)=0.
   The genuine local upper-quadratic bound, plus positive radii, makes the
   penalty/t^2 limsup<=0. Mere C1 stationarity of Phi is insufficient and
   has NOT replaced that assumption. K can be negative. Output norms need
   not have a uniform equivalence constant across n.
5. Sharpness is an optimization over w<=M: choose the actual constant
   repair M and a spectral observation. It is NOT claimed that an arbitrary
   prescribed C or prescribed negative/variable repair attains the budget.
   High and low terms are orthogonal; the sufficiency estimate is global.
6. Strict cutoff equality checked in dimension1 on a diagonal quadratic
   example: if (1+M)*lambda=c, that coordinate needs no observation.
   Conversely lambda=0 with c>0 always needs observation. These are analytic
   boundary examples, not software test outputs.
7. Real frequency bookkeeping: one nonzero conjugate pair carries twice
   its per-frequency complex multiplicity and counts as two residues.
   A self-conjugate even-n frequency carries its real kernel dimension
   once. There is no extra universal factor2. Zero divergence rank is0,
   not1; constants have multiplicity aD. For n=1 the proposed formula gives
   exactly aD; for the D=1 boundary (outside the coexact theorem's D>=2
   scope) it reduces to a constants for every n, consistent with the prior
   one-dimensional counterexample.
8. n=2 normalization is fixed by forward differences, not a simple graph
   with identified neighbor edges. Squared symbol is4sin^2. This matches
   the existing actual operator even at Nyquist frequencies.
9. Counting bound uses centered representatives and an OPEN spectral cutoff.
   Integer points in a real centered interval of radius B are at most1+2B.
   Nyquist endpoints have one chosen representative. The comparison constants
   in the order statement may depend on c,D,Nc; no universal constants or
   exact optimal coefficient are claimed there.
10. Small-frequency equivalent (11) requires BOTH M_n->infinity and
    M_n=o(n^2). Fixed M has a different limiting fraction of the Brillouin
    zone and cannot be inserted into (11). At M~beta*n^2 only bounded order
    is claimed; resonant limiting shells require additional analysis.
11. Bibliography locator initially drafted as section2.2/printedp4 was
    corrected after opening the primary PDF: actual section2.1, printedp5,
    PDF index4. The source supports the scalar torus eigenvalue formula;
    it is not credited with proving the observation classification.
12. Remaining formal debt: new family quantifiers and limits; full physical
    Fourier decomposition and real low-space multiplicity; optimal projection
    construction; counting and asymptotic transport. No later Lean or oracle
    evidence has yet been run for any of these new assertions. The prior
    six finite endpoints retain only their own original assurance.

No exhaustive priority search, numerical experiment, independent review,
new PDF, deposit, licence, model assessment or physical hypothesis elimination
was performed. The analytic deduction is grouped with the existing article.
All strict inequalities, scale and regularity restrictions above are material.
