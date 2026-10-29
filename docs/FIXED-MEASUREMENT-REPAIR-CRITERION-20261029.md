# When a fixed measurement admits any finite penalty repair

Analytic extension of the flat coarse-rank dossier, 29 October 2026.
Source context: main `85c5a1b32dd0872ea807f5da148d862cabfb48b0`,
Fourier construction `0e88dfe5f434123e057dd83c17801872fc2498a5`.
This is a complete finite-dimensional paper proof, not a Lean verification,
an independent review, or a new standalone paper. It does not complete the
remaining concrete cochain L2/energy formalization.

## The ambiguity removed

The rank budget in `FLAT-COARSE-RANK-OBSTRUCTION-20261029.md` is necessary.
Meeting it, or detecting each low eigenvector, does not suffice for a specified
measurement. Even the non-strict target inequality on its entire kernel can
fail to suffice. The missing issue is coupling of a kernel direction at the
target energy to a measured direction. A nonlinear penalty cannot fix that
coupling, since it is constant on each measurement fibre.

Throughout, E and F are finite-dimensional real inner-product spaces, C:E->F
is linear, H:E->E is self-adjoint, c>0, and B=H-cI. A previously chosen
self-adjoint fine repair V may be included by replacing H with H+V; it is not
chosen during the theorem. The sought penalty is a finite-valued function
Phi:F->R with Phi(0)=0, satisfying

    <x,Hx> + Phi(Cx) >= c ||x||^2                 for every x.       (1)

No continuity, convexity, positivity or homogeneity of Phi is assumed.
Finite-valued matters: assigning infinity to every nonzero output is excluded.

## Exact criterion for a fixed C

Put N=ker C and W=N-perp. Relative to E=N direct-sum W write

    B = [ A  D  ] ,   A:N->N, D:W->N, G:W->W.
        [ D* G  ]

The following statements are equivalent:

1. Some finite-valued Phi with Phi(0)=0 satisfies (1).
2. A is positive semidefinite and ker A is contained in ker D*.
3. There is a scalar a>=0 such that (1) holds with Phi(y)=a||y||^2.

Thus allowing an arbitrary nonlinear penalty adds no existence power to an
unbounded quadratic penalty for this finite-dimensional, fixed-measurement
problem. This says nothing about uniform bounds on a in a varying family.

### Necessity, including the singular case

For u in N, (1) gives <u,Au>>=0, so A is positive semidefinite. For z in
ker A and any v in W, C(tz+v)=Cv for all real t. Expanding the left side of
(1) minus its right side gives

    2t <z,Dv> + <v,Gv> + Phi(Cv).

It cannot stay nonnegative for all t unless <z,Dv>=0. Hence D*z=0 for every
z in ker A. This argument uses the actual values on whole fibres, not only
the low eigenvectors of H.

### Sufficiency, with a finite quadratic choice

Assume condition 2. Since A is self-adjoint, range A=(ker A)-perp; the
coupling condition therefore gives range D contained in range A. Define
A-dagger to invert the positive eigenvalues of A and to be zero on ker A.
Then A A-dagger D=D. Direct expansion, using self-adjointness, gives

    <u+v,B(u+v)>
      = <u+A-dagger Dv, A(u+A-dagger Dv)>
        + <v,Sv>,          S=G-D* A-dagger D.                       (2)

The first term is nonnegative. If W is nonzero, C restricted to W is
injective; compactness of its unit sphere gives a number sigma>0 such that
||Cv||>=sigma||v||. Let mu be the smallest eigenvalue of S and choose

    a = max(0,-mu) / sigma^2.

Then <v,Sv>+a||Cv||^2>=0, proving (1). If W=0, C=0 and A=B is already
positive semidefinite; choose a=0 without introducing sigma or mu. Conversely,
condition 3 is a particular case of condition 1. This covers all dimensions,
including the zero-dimensional domain.

## A two-dimensional falsifier for two tempting sufficiency claims

Let H=diag(0,2), c=1, and C_beta(x,y)=x+beta*y. For every beta, the single
eigendirection below c is detected, and rank C_beta=1 equals its dimension.
For beta=1 the entire kernel also satisfies the target bound with equality:
H(t,-t) has quadratic energy 2t^2 and the squared norm is 2t^2.

Nevertheless no finite-valued penalty can work. For x=t, y=1-t, the output
is always 1 and

    <(t,1-t),(H-I)(t,1-t)> + Phi(1) = 1-2t+Phi(1),

which is negative for sufficiently large t. This refutes both
"rank budget plus detection suffices" and "nonnegative target form on the
measurement kernel suffices", even when combined, for a specified map.
It does not refute the earlier necessary rank theorem.

The full family gives a sharp diagnostic. On ker C_beta, B has value
(1-beta^2)y^2. Thus |beta|>1 fails already on the zero fibre; |beta|=1 fails
by the nonzero coupling just exhibited (replace the sign of y if necessary).
For |beta|<1 a quadratic penalty works exactly when

    a >= 1/(1-beta^2).

Indeed the repaired B matrix is

    [ a-1     a*beta       ]
    [ a*beta  1+a*beta^2   ],

whose determinant is a*(1-beta^2)-1. At or above the displayed threshold
its first diagonal entry is nonnegative and the second is positive, so it
is positive semidefinite; below it the determinant or a diagonal is negative.
Although all these measurements have the same rank and detect the low mode,
the required amplitude diverges as |beta| approaches 1 from below.

## Sharp rank capacity when the map itself may be designed

For comparison assume H is positive semidefinite and let K_c be the number
of its eigenvalues strictly below c, counted with real multiplicity. Allow
the choice of a measurement into R^M and a positive semidefinite fine repair
V of rank at most r, with no amplitude or locality constraints. Such choices
can satisfy (1), with H replaced by H+V, if and only if

    K_c <= M+r.                                                   (3)

Necessity: on the K_c-dimensional strict low spectral subspace every nonzero
vector has H-Rayleigh quotient strictly below c. If its dimension exceeds
M+r, the joint map (C,V) has a nonzero kernel vector there, contradicting
(1). This does not need an eigenvalue theory for nonlinear Phi.

Sufficiency: choose a real orthonormal eigenbasis. Split the K_c low basis
vectors into J of size at most M and T of size at most r. Set Cx to their
J-coordinates, padded with zeros, set Phi(y)=c||y||^2, and set V=c P_T.
Each formerly low eigenvalue receives c, and all remaining eigenvalues were
already at least c. Since H is positive semidefinite, the target follows.
When K_c=0 take C=0,V=0,Phi=0. Eigenvalues equal to c need no repair; replacing
"strictly below" with "at most" would give a false necessary budget.

This is an existential construction of generally global measurements. It
does not prove sufficiency for an existing block map, locality-preserving
measurement, bounded amplitudes or a uniformly conditioned family. The
fixed-map criterion and beta example identify precisely why that distinction
matters. For a non-PSD H the same construction can use the individual positive
weights c-lambda_j instead; the PSD version is enough for the flat Hodge form.

## Consequences for the flat programme and novelty boundary

The low-mode rank obstruction remains intact. At unit spacing the torus Hodge
spectrum from the previous analytic note makes the exact required budget

    K_c = d*m * #{ k in (Z/nZ)^d : 4 sum_i sin^2(pi*k_i/n) < c }.

The real count is valid also at self-conjugate/Nyquist frequencies: the real
symmetric matrix and its complexification have the same eigenvalue
multiplicities. One must not double the complex frequency count. The actual
Hodge symbol identity and real spectral transport remain analytic, pending
the cochain formalization; (3) does not silently formalize them.

For designing repairs, low-mode detection alone is therefore an inadequate
judge. Use the kernel compression and its singular coupling, then test
conditioning and amplitude uniformly in the actual lattice parameters.
Physical spacing rescales H and changes K_c. No physical mass gap, continuum
result, hRpoly producer or change to PR29's 20/41 and TermSource=0 follows.

These are classical finite-dimensional mechanisms. The spectral argument is
an application of the min-max principle; see David Bindel's author-written
[Cornell lecture](https://www.cs.cornell.edu/courses/cs6210/2025fa/lec/2025-11-03.html).
The singular block condition belongs to generalized Schur-complement theory:
Arthur Albert, [SIAM J. Appl. Math. 17 (1969), 434-440,
DOI 10.1137/0117041](https://epubs.siam.org/doi/abs/10.1137/0117041), and
Li and Mathias, [SIAM Review (2000),
DOI 10.1137/S0036144599337290](https://epubs.siam.org/doi/abs/10.1137/S0036144599337290).
The publisher pages were checked; Albert's full text was not accessed, so no
specific numbered theorem or quote from its body is claimed. The argument
above is supplied in full. The classical torus spectrum is discussed by
Lin, Wan and Zhang, [arXiv:2403.06105v1](https://arxiv.org/html/2403.06105v1).
No priority or literature-wide novelty claim is made. Group this result with
the existing obstruction dossier rather than issuing a paper of corollaries.

## Assessment and verification context

This note was derived and checked algebraically by the same Codex assistant
in the same chat. It is not an independent model assessment or human peer
review; no score was requested or transferred from another artifact. No Lean
build or numerical test of this note has been performed. The beta determinant,
fibre counterexample, completion of squares, empty-space case and equality
threshold were checked explicitly above. The falsifiers are a wrong fibre
expansion, a missing range condition in (2), or a real-multiplicity error.
