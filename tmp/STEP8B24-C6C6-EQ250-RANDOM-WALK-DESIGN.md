# Step 8b.24 C6c.6 — CMP96 (2.50), (2.60)--(2.66)

Status: primary-source contract and reusable norm algebra fixed statically;
no C6c.6 producer, `.olean`, focal or axiom verdict exists.

## Literal source chain

CMP96 printed pp. 231--234 gives the following finite chain.

1. Define the multiscale owner set `B = union_j Lambda_j` and the distance
   `d(y,y')` by the infimum of the scale-weighted length of admissible
   contours, (2.45)--(2.46).
2. Decompose a minimizing contour across adjacent scale surfaces and prove
   the lower bound (2.48).  In particular, transitions between distinct
   adjacent surfaces pay the physical separation `R M`, (2.57).
3. From the single-cell estimate (2.44), sum the physical cells in (2.38) to
   obtain both the unweighted `L-infinity` defect bound `O(M^-1)`, (2.49),
   and the owner-localized exponential bound (2.51).
4. For `0 < alpha < 1`, reserve the fraction `alpha` of the decay for the
   owner convolution and retain `(1-alpha) delta0` in the endpoint factor,
   (2.54)--(2.56).
5. Define

   ```text
   c0(alpha) = sum_{z in Z} exp(-alpha delta0 |z|)
   c1(alpha) = 12 * c0(alpha/2)^d.
   ```

   Under the literal separation window

   ```text
   (1/4) * alpha * delta0 * R * M
     > 2*d*log(c0(alpha/2)) + 1,                              (2.59)
   ```

   Lemma 2.1 proves the one-row sum (2.61) and its convolution powers
   (2.62)--(2.63).
6. The physical defect powers therefore have amplitude

   ```text
   (defectAmplitude * c1(alpha))^n
   ```

   at the unchanged endpoint rate `(1-alpha) delta0`, (2.64)--(2.65).
   The geometric series in (2.50) converges when this displayed amplitude is
   strictly below one and yields (2.66).

The source later specializes to `alpha = 1/2`, but the formal interface should
retain `alpha`, (2.59), and `c1(alpha)` explicitly until a joint scalar witness
is chosen.

## Orientation gate

The sum in CMP96 (2.61) fixes the output owner `y` and sums source owners
`y'`.  This is the row orientation that acts on the global supremum norm.

The older generic predicate `FinitePiLpTypedWeightedRowKernelBound` fixes a
source and sums targets.  It is valid same-rate algebra but is not the C6c.6
norm, and no abstract adjoint/symmetry argument transports its constant.

The correct sealed substrate already exists:

* `FinitePiLpTypedOwnerSupKernelBound` records the complete owner-fibre
  action by a nonnegative coefficient matrix;
* `FiniteOwnerWeightedRowBound` fixes the output and sums sources;
* `FinitePiLpTypedOwnerWeightedSupKernelBound` bundles the two;
* `finiteOwnerWeightedRowBound_convolution` is same-rate
  submultiplicativity in the correct orientation;
* `finitePiLpTypedOwnerWeightedSupKernelBound_neumann` constructs the literal
  operator `tsum` and its coefficient `tsum` under one strict contraction.

Thus C6c.6 needs no new generic norm algebra.  It needs the source-specific
multiscale owner/distance dictionary and a sign-correct C6c.5 coefficient.

## Measured gap between the existing physical row and C6c.6

`cmp99Eq389SourceLocalizedRegionalDefect_ownerWeightedSup` already produces
an output-fixed owner row, but it is not yet the C6c.6 endpoint:

* it is built over the current plus-sign three-species operator rather than
  the sign-correct literal `K(h)` fixed by C6c.5;
* it takes the full four-action Green certificate instead of the C6c.4
  value/left-derivative pair;
* its owner is the single-scale `FinBox 4 (2*(K*Q))` with `finBoxDist`, not
  the dependent multiscale owner set and distance of (2.45)--(2.48);
* its shell factor is the generic ball-counting
  `cmp99OmegaSiteExpSumBound`, not the explicit (2.59)--(2.61) source sum.

Its output-fixed conversion pattern and the complete Neumann algebra are
reusable after those source-specific repairs.

## Required construction

1. Define a proof-carrying finite owner type representing the disjoint
   multiscale union in (2.45), including the `j` versus `j+1` branches already
   fixed by C6c.4.  Do not quotient owners from different scales merely
   because their carriers overlap.
2. Define the admissible-contour distance (2.46).  Prove zero diagonal and
   triangle inequality as the exact inputs to the sealed convolution algebra.
3. Formalize the surface-crossing decomposition (2.47) and lower bound
   (2.48), including the adjacent-scale separation (2.57).  An arbitrary
   metric with these facts supplied as hypotheses is not a source producer.
4. Prove the literal scalar window (2.59), the definitions of `c0`/`c1`, and
   the output-fixed owner row (2.60)--(2.63).  The quantifier order must choose
   `alpha`, `delta0`, `R`, and `M` before the row is consumed.
5. Transport the sign-correct C6c.5 single-cell action through the cell sum
   without ambient cardinality, obtaining the literal regional defect and
   the displayed contraction amplitude
   `defectAmplitude * c1(alpha)`.
6. Require and prove this concrete amplitude `< 1`.  Do not replace it with a
   free operator-norm hypothesis.  This is the source-specific attainment of
   the Neumann window for the fine regional defect.
7. Apply the sealed output-fixed owner powers/Neumann algebra at rate
   `(1-alpha)*delta0`, construct `G'_0 * sum_n R^n`, and identify it with the
   canonical generated Green by the existing inverse-uniqueness pattern.

## Acceptance endpoint and exclusions

C6c.6 ends with the literal random-walk/Neumann Green of (2.50), its exact
inverse identity, and the value action (2.66) at a positive retained rate.
It may also expose the common Neumann coefficient needed by C6c.7.

It does not receive a family of walk sums, a prechosen inverse, convergence,
or a bare `norm R < 1` as data.  It does not yet prove the derivative,
right-adjoint or Laplacian actions of Proposition 2.2; those are C6c.7.  It
does not claim the gauge dictionary of Corollary 3.6 or the terminal physical
certificate.

