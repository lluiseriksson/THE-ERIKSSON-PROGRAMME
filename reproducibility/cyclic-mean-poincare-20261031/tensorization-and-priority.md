# Unit044: cyclic component and remaining physical transport

The candidate module derives the actual arithmetic-mean estimate on ZMod n,
for n>0 and any real normed vector space V, with counting L2:

    sum_x ||f(x)-mean(f)||^2 <= n^2 sum_x ||f(x+1)-f(x)||^2.

No supplied Poincare certificate, spectral-gap field, or postulated comparison
appears among the hypotheses. The coefficient is deliberately nonoptimal.
Its verification status is determined by the reproduction reports, not this note.

## One continuing question: actual quadratic-weight counterexample

For G=(ZMod n)^D, define T_a f(x)=f(x+a), e_j the actual unit coordinate.
The generic translation estimates already reduce the remaining argument to
the finite coordinate decomposition a=sum_j a_j.val*e_j. Triangle inequality
gives ||T_a f-f|| <= n sum_j ||T_ej f-f||. Averaging all translations gives
f-mean(f), with the actual cardinal n^D and its inverse cancelling. Cauchy
Schwarz then yields

    ||f-mean(f)||^2 <= D*n^2 sum_j ||T_ej f-f||^2.

This direct finite-group route avoids introducing an unproved tensorization
certificate. It has not yet been Lean-checked for the multidimensional torus.
The next task must prove the coordinate decomposition and actual averaging
identity, then transport through the repository's FinBox representation and
componentwise physical gradient. For inner-product-valued cochains prove the
orthogonal identity

    ||f||^2 = ||f-mean(f)||^2 + n^D ||mean(f)||^2.

Consequently actual weights D*n^2 and the actual output penalty
Phi_n(y)=n^D||y||^2 should give global coercivity coefficient1 with a fixed
mean-output dimension D*(Nc^2-1). The n-dependent penalty is permitted by the
retained hypotheses; its quadratic constant is not uniform1. This conclusion
remains analytic until the actual operators and identities are checked.

Falsifiers: a coordinate-wrap/counting error, nonzero mean-zero zero-energy
field, or failed mean/gradient normalization. After three units with no useful
mathematical progress record the concrete obstacle and change route. This is
one question, not a new parallel research programme.

## Originality and relevance

Primary author-hosted source consulted on 2026-10-31:
David A. Levin and Yuval Peres, Markov Chains and Mixing Times, 2nd edition,
with contributions by Elizabeth L. Wilmer:
https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf
Section13.4, printedpp187-190, Theorem13.20 and Corollary13.21 describe energy
comparison via paths and the associated Poincare/spectral-gap bound. The
following torus example has quadratic-size relaxation. These establish that
the scalar mechanism and quadratic scale are classical. Our inference is that
the vector-valued translation implementation is a formal transport utility,
not a new mathematical discovery. This limited source check does not establish
priority for the repository's complete actual-map obstruction/counterexample.

Relevance here is to test exactly why a common weight cap cannot simply be
discarded in the flat finite-lattice rank obstruction. Neither the cyclic
estimate nor the proposed counterexample establishes interacting Yang-Mills,
continuum convergence or a physical mass gap. No stand-alone paper is warranted
for this utility; keep it with the existing coarse-information dossier.
