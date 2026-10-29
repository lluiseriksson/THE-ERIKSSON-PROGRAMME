# Fixed-dimensional coarse measurements cannot repair the full flat form

Analytic research note, 29 October 2026. Source definitions inspected at
`628a71f677f3808404d3323acabdc94db84ddefc`. This is a paper proof using classical
Fourier analysis and rank-nullity, not a compiled Lean theorem or a priority
claim. It belongs with the existing flat obstruction dossier, not in a separate
paper of corollaries.

## Question and rejection criterion

Can replacing the original block average by an arbitrary linear map into the
same fixed coarse field space restore coercivity uniform in block side, on the
unrestricted, periodic, unit-spacing flat domain?

Fix dimension d >= 2, internal real dimension m >= 1 and coarse side N' >= 1.
Let n = L N', q = d m, and E_n be the real positive-bond one-cochains on
(Z/nZ)^d with m internal coordinates. Its dimension is q n^d. Let K_n be the
flat Hodge form curl*curl + div*div with one plaquette per site and unordered
direction pair. Let C_n:E_n -> F_n be any linear measurement, and let Phi_n be
any real functional with Phi_n(0)=0. Neither locality nor bounds on its size,
continuity or positivity are assumed. Let V_n be a positive semidefinite
self-adjoint fine-space operator. Write M_n=dim F_n and r_n=rank V_n.

The proposed repair asks for one c>0, independent of L, satisfying

    c ||A||^2 <= <A,K_n A> + Phi_n(C_n A) + <A,V_n A>       (1)

for every A and every L. The mechanism below is a low-frequency test space
larger than the combined number of measured/lifted directions. A concrete
counterexample to its Fourier identity, its real dimension, or its kernel
intersection bound falsifies this argument. Stop this route after three units
without a verified reduction; do not replace the missing bound by an assumption.

## 1. A general dimension obstruction

Suppose S is a real subspace on which <A,K_n A> <= b ||A||^2, where b<c.
Then (1) requires

    dim S <= rank(C_n restricted to S) + rank(V_n restricted to S)
          <= M_n + r_n.                                  (2)

Proof: apply rank-nullity to A -> (C_n A,V_n A) on S. If dim S exceeds the
right side, a nonzero A lies in S intersect ker C_n intersect ker V_n. Both
repair terms vanish there, including the possibly nonlinear Phi_n term.
Equation (1) then gives c||A||^2 <= b||A||^2, impossible. Positivity of V_n
is natural for a repair but is not needed for this necessary dimension bound.

In the linear penalty case this is the usual finite-rank min-max obstruction.
For comparison, the classical matrix interlacing inequality is stated in
Berkolaiko, Cox, Latushkin and Sukhtaiev, *The Duistermaat index and eigenvalue
interlacing*, Introduction (1.1),
[DOI 10.4171/JST/590](https://ems.press/content/serial-article-files/52264?nt=1).
The nonlinear Phi_n case here uses the direct kernel argument, not eigenvalues
of a nonlinear functional.

## 2. Full flat Fourier band and real dimension

Choose an integer R>=0 with 2R<n. Let S_R contain the fields supported in the
Fourier cube k in {-R,...,R}^d. The cube is invariant under k -> -k; since
2R<n its residues are distinct and only k=0 is self-conjugate. Each nonzero
pair gives two real scalar modes, while k=0 gives one. Consequently

    dim_real S_R = q (2R+1)^d.                            (3)

This is a count of real fields, not a doubling of the complex dimension.

Here is the flat Hodge symbol calculation, so no transfer from a differently
normalized graph operator is assumed. Put z_i=exp(2 pi i k_i/n)-1 and let a_i
be the complex amplitude in direction i, first for one internal coordinate.
The curl amplitudes are z_i a_j-z_j a_i. The backward divergence amplitude
is -sum_i conjugate(z_i) a_i. Expanding the squares gives

    sum_{i<j}|z_i a_j-z_j a_i|^2
      + |sum_i conjugate(z_i) a_i|^2
      = (sum_i |z_i|^2)(sum_i |a_i|^2).                 (4)

The mixed terms cancel pairwise. Sum over internal coordinates and use Fourier
orthogonality. Thus the flat Hodge eigenvalue on frequency k is

    lambda(k) = 4 sum_i sin^2(pi k_i/n),

and every A in S_R satisfies

    <A,K_n A> <= 4 pi^2 d R^2/n^2 ||A||^2.              (5)

The source stencils are `covariantD1CLM_trivial_apply`,
`gaugeConstraintQCLM_trivial_apply` and `flatGaugeHodgeK0_inner_right` in
`YangMills/RG/PhysicalGaugeCochains.lean`. Their signs and unordered-plaquette
convention agree with (4). This analytic diagonalization is not already a Lean
declaration merely because those stencils are formalized.

The scalar discrete-torus spectrum is classical; see Lin, Wan and Zhang,
*Connection Laplacian on discrete tori with converging property*,
[arXiv:2403.06105v1, Theorem 1.2](https://arxiv.org/html/2403.06105v1).
Equation (4) supplies the one-cochain specialization used here.

## 3. Arbitrary changed coarse map: a necessary rank budget

Combining (2)-(5), whenever 4 pi^2 d R^2/n^2<c, a repair satisfying (1) must have

    M_n + r_n >= q (2R+1)^d.                            (6)

For a uniform c>0, set a=min(1/4,sqrt(c)/(4 pi sqrt(d))) and R=floor(a n).
Then 2R<n and the bound in (5) is at most c/4<c. Therefore

    M_n + r_n >= q (2 floor(a n)+1)^d.                  (7)

In particular the required total dimension/rank grows at least proportionally
to n^d at fixed c,d,m. This is a necessary condition, not a sufficient one.

For the usual coarse output space, M_n=q(N')^d is fixed while L varies.
With V_n=0, **no choice of linear replacement C_n into that space** can restore
the uniform full-space unit-spacing gate. C_n need not factor through the old
Q, be local, commute with translations, or preserve its Fourier witness. It may
lift that particular witness while leaving another low-frequency vector unseen.
Adding only a bounded-rank fine term cannot change this conclusion either.

For V_n=0 there is a particularly simple bound independent of N'. Take R=N'
and L>=3, so 2R<n. Then

    dim S_R = q(2N'+1)^d > q(N')^d = M_n.

For every changed linear coarse map there is consequently a nonzero A in
ker C_n with

    <A,K_n A>/||A||^2 <= 4 pi^2 d/L^2.                  (8)

Thus any valid full-space Poincare constant for this changed-map repair must
obey CP(L)>=L^2/(4 pi^2 d), regardless of the amplitude, locality or mixing of
the changed measurement or the nonlinear penalty after it. The missed vector
may depend on C_n; no single universal vector annihilates every possible map.
For d=4 the explicit denominator is 16 pi^2. This quantitative statement removes
the need to hypothesize that a replacement map preserves the original witness.

A quantitative finite-rank version avoids asymptotic notation. If M_n+r_n<=B
uniformly, choose the least integer s>=0 with q(2s+1)^d>B. For n>2s, rank-nullity
supplies a nonzero missed field of Rayleigh quotient at most
4 pi^2 d s^2/n^2. If s=0, it supplies an exact constant zero mode.

## 4. Limits and novelty assessment

This closes the changed-linear-map-only escape **within these conventions**.
It strengthens the diagnosis of the existing paper's Section 10: detecting its
one exhibited Fourier line is insufficient, and fixed coarse output dimension
prevents repairing the full form by a replacement measurement alone.
It does not amend the paper's proven no-go, identify an error in its theorem,
or rule out a measurement whose output dimension grows with the fine volume.

The implication is an application of standard Fourier spectra, min-max and
rank-nullity. The targeted repository search found no statement of this budget;
that does not establish literature novelty. No separate publication or original
spectral theorem is claimed. The operational value is eliminating an entire
proposed repair family rather than changing the old map's kernel by hypothesis.

At physical spacing eta, K_n is multiplied by eta^-2. Then (5) has the same
factor, and the low-band threshold is R/n < eta sqrt(c)/(2 pi sqrt(d)). With
eta=1/L and fixed N', the preceding volume-growth conclusion does not follow.
Gauge-restricted domains, actual background operators, nonlinear measurements
(as opposed to nonlinear penalties after a linear measurement), and unrestricted
rank fine Hessians are also outside this no-go.

No hRpoly assumption is discharged, no term source is created, and no physical
mass gap or continuum statement follows. The canonical PR29 count remains
20/41 with TermSource=0. Formalization and external scientific review remain
separate tasks; this note is a complete on-paper argument only.
