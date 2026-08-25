# Eq. (3.37) complex forced finite recursion

Status: DESIGN ONLY / PRE-VALIDATION.  No `.olean`, compiler, or axiom-oracle
verdict exists for the proposed modules below.

Source checkpoint inspected: `c1ec63d9b17f6412f59a8194a6f71d5de7c4800f`.

## Existing source-facing leaf

`cmp99Eq337SourceComplexLocalizedNextBackground` constructs one coarse
`SL(N,C)` background internally from the literal physical inputs

- `U`,
- the Eq. (3.37) one-cochain `A`,
- `eta`, `epsilonU`, and `rA`, and
- the proved link, small-field, and no-winding inequalities.

It does not accept a preselected coarse background or a free deviation
family.  This is the correct one-step leaf, not yet a finite recursion.

## Existing recursion pattern

`BalabanCMP99SourceLocalizedRetainedTower.lean` already contains the private
recursion `cmp99SourceLocalizedCanonicalRetainedAux`.  It constructs every
localized and canonical prefix internally and proves the prefix-Qprime
equalities.  No scale-indexed background or tower family is caller data.

The complex recursion must reuse this logical pattern.  It must not accept a
finished family `Fin (depth + 1) -> background` or per-scale equalities.

## Actual missing producer

The complex one-step output currently has no theorem bounding

```lean
‖(nextBackground e : Matrix (Fin Nc) (Fin Nc) C) - 1‖
```

uniformly on every oriented coarse edge.  Without that theorem, a recursive
interface would have to receive the next small-field fact as an input, which
would merely rename the pending obligation.

The required producer is source-internal and has four stages.

1. Reuse the probability-vector identity for the source block weights.
2. Prove the `SL(N,C)` exponent estimate with the existing
   `MatrixNearLogNoWindingBudget`; this is the same Banach-algebra estimate as
   the sealed unitary producer and does not use unitarity.
3. Bound the coarse source transport directly by the complex Wilson-line
   estimates.  Its literal path has length `M`; no unitary norm-one weakening
   is permitted.
4. Use the literal product identity

   ```text
   F * C - 1 = (F - 1) * C + (C - 1)
   ```

   so the factor norm and coarse deviation remain separate and visible.

For an oriented-link radius `r` and no-winding budget `B`, the first honest
candidate positive-edge recurrence is

```text
r_next = cmp99UbarExpRadius(B) * (1 + r)^M
       + M * r * (1 + r)^M.
```

This is a candidate definition to be compiled, not a claimed theorem.  The
two summands must remain separate in the Lean definition and audit.

This positive-edge radius is not yet an oriented-link radius.  The generated
configuration reconstructs a negative edge by group inversion, and inversion
in `SL(N,C)` is not an isometry.  If the positive radius is `q < 1`, the
Banach-geometric inverse estimate gives the next candidate

```text
r_oriented_next = q / (1 - q).
```

The proof must identify the matrix inverse of the determinant-one group
element with the geometric inverse of `1 - (1 - U)`.  A unitary
`norm_inv_sub_one = norm_sub_one` lemma is forbidden here.  The strict gate
`q < 1` is a condition on the flowing radius and belongs in the inductive
chain itself; it is not to be mislabeled as another freely chosen window in
the global joint-smallness record.

## Forced chain after the producer

Only after the preceding output bound compiles should the tree introduce a
scalar inductive chain analogous to `CMP99SourceUbarRadiusChain`:

```text
stop : nonnegative r -> chain 0 r
step : nonnegative r
    -> literal no-winding gate for r
    -> cmp99UbarLogRadius(B(r)) < 1
    -> positive_next(r) < 1
    -> chain depth (positive_next(r) / (1 - positive_next(r)))
    -> chain (depth + 1) r
```

The recursion then takes one initial complex background and this scalar
chain, constructs each next background internally, and returns the terminal
background (and, if a consumer needs it, private prefixes plus public
projection lemmas).  It must not accept a background family, a free `hdev`, a
free next-background smallness proof, or a terminal equality.

This is the low-level recursion interface, not the closed physical endpoint.
The source-facing endpoint must also construct the finite scalar `chain` from
the literal initial radius and one named joint scalar-regime witness.  Merely
accepting `CMP99SourceComplexUbarRadiusChain` from the caller would package the
per-scale strict gates without discharging them and therefore does not count
as physical closure.

The sealed real-slice template is `CMP99SourceUbarClosedBudget`: it defines the
generated radius at every depth, proves an explicit one-step growth factor,
and derives the complete chain from one initial-scale `terminal_small`
inequality.  The complex producer must have the same closed shape for the
literal oriented radius map above.  A replacement record containing
`∀ k < depth, ...` smallness fields is not accepted; that would only rename the
per-scale obligations.

One conservative compiler target, to be proved rather than assumed, is as
follows.  Choose `R > 0`, put `L = d * (M - 1)`,

```text
F_delta(R) = (1 + R)^L
C_delta(R) = L * (F_delta(R)^4 + F_delta(R)^3
                    + F_delta(R)^2 + F_delta(R))
C_q(R) = (4 * C_delta(R) + M) * (1 + R)^M
K(R) = max 1 (2 * C_q(R)).
```

For `0 ≤ r ≤ R`, the literal four-Wilson-line expression should give
`deviation(r) ≤ C_delta(R) * r`.  Under
`C_delta(R) * r < 1/4`, the exact logarithm and exponential remainders give
`q(r) ≤ C_q(R) * r`; under `C_q(R) * r < 1/2`, the oriented inverse loss gives
`next(r) ≤ K(R) * r`.  Thus one inequality of the form

```text
K(R)^depth * r0 <
  min R (min ((min noWindingThreshold (1/4)) / C_delta(R))
             (1 / (2 * C_q(R))))
```

is the intended closed producer.  The extra `1/4` is not redundant: the
physical no-winding threshold can be larger, whereas the compiled linear
exponential estimate uses the stricter quarter-radius regime.  The divisions
require their own positivity lemmas, and the displayed constants are a design
target until Lean compiles them; they are not evidence or a source claim.

The exact scalar shape to elaborate after the prerequisite gate is therefore
the following (names remain provisional until Lean fixes the implicit
arguments):

The generated radius itself must be proof-free.  In particular, the recursion
first defines scalar functions of the literal deviation radius (`log`, `exp`,
positive-edge `q`, and `q / (1 - q)`) and only afterwards proves that they are
definitionally or propositionally equal to the values obtained from
`cmp99SourceComplexUbarNoWindingBudget`.  Recursing directly on a term whose
value contains the proof `hnoWinding` would make `radiusAt` proof-dependent and
would obstruct the closed-budget induction for no mathematical reason.  The
Mathlib-only reproduction
`tmp/CMP99ComplexClosedRadiusScalar.repro.lean` freezes this proof-free scalar
boundary before it is imported into project source.

```lean
inductive CMP99SourceComplexUbarRadiusChain (d M Nc : ℕ)
    [NeZero d] [NeZero M] [NeZero Nc] : ℕ → ℝ → Prop
  | stop (r : ℝ) (r_nonneg : 0 ≤ r) :
      CMP99SourceComplexUbarRadiusChain d M Nc 0 r
  | step {depth : ℕ} (r : ℝ) (r_nonneg : 0 ≤ r)
      (hnoWinding :
        cmp99Eq337SourceComplexUbarUniformDeviationRadius d M r <
          cmp99UbarNoWindingThreshold Nc)
      (hlog : cmp99UbarLogRadius
          (cmp99SourceComplexUbarNoWindingBudget d M Nc r hnoWinding) < 1)
      (hq1 : cmp99SourceComplexUbarNextLinkRadius M r
          (cmp99SourceComplexUbarNoWindingBudget d M Nc r hnoWinding) < 1)
      (tail : CMP99SourceComplexUbarRadiusChain d M Nc depth
        (cmp99SourceComplexUbarNextOrientedLinkRadius M r
          (cmp99SourceComplexUbarNoWindingBudget d M Nc r hnoWinding))) :
      CMP99SourceComplexUbarRadiusChain d M Nc (depth + 1) r
```

Thus `hq1` travels with the flowing radius at the exact step where inversion
consumes it.  It is neither caller-supplied linkwise smallness nor a field of
the global fourteen-window compatibility record.

For Eq. (3.37), the public finite constructor must start from the literal
background

```lean
cmp99Eq337PhysicalComplexPerturbedBackground U A eta
```

and the already proved radius
`cmp99Eq337PhysicalComplexPerturbedLinkRadius Nc epsilonU eta rA`.  The
perturbed background is built in the body, not exposed as an argument.  A
private dependent recursion may retain prefixes, but the public output is the
terminal generated background and its derived all-orientation radius theorem.
This distinction prevents the generic one-step prerequisite (which correctly
takes its current background) from leaking a freely selected background into
the source-facing Eq. (3.37) recursion.

The lattice index should follow the already sealed source recursion exactly:
an input at
`cmp99RegionalLatticeSize M N depth` is coarsened once in each `step`, and
the terminal output lives at `N`.  In particular, the public source-facing
shape is constrained to

```lean
noncomputable def cmp99Eq337SourceComplexRecursiveBackground
    ...
    (U : PhysicalGaugeBackground d
      (cmp99RegionalLatticeSize M N depth) Nc)
    (A : CMP99Eq337PhysicalComplexOneCochain d
      (cmp99RegionalLatticeSize M N depth) Nc)
    (eta epsilonU rA : ℝ)
    ...
    (chain : CMP99SourceComplexUbarRadiusChain d M Nc depth
      (cmp99Eq337PhysicalComplexPerturbedLinkRadius
        Nc epsilonU eta rA)) :
    GaugeConfig d N (Matrix.SpecialLinearGroup (Fin Nc) ℂ)
```

The depth-zero branch returns the internally constructed perturbed
background after the definitional lattice-size reduction.  The successor
branch applies `cmp99SourceComplexLocalizedNextBackgroundOfLinkRadius`,
derives its all-orientation bound from the head of `chain`, and recurses on
`chain.tail`.  This is the only accepted recursion direction: a terminal
background lifted back to the fine lattice, or a caller-supplied tail
background, would reverse the physical construction.

## Acceptance gates

1. The final source-facing leaf still constructs the first perturbed
   background from literal `U`, `A`, and `eta`.
2. The public recursive constructor has no argument whose type is a
   scale-indexed background family.
3. The public recursive constructor has no free `hdev` or per-scale
   small-field hypothesis for internally generated backgrounds.
4. A closed source-facing producer constructs the scalar radius chain; the
   existence of the low-level constructor with `chain` as an argument is not
   a terminal producer and cannot retire this obligation.
5. Both orientations are proved; negative edges are not inherited from the
   unitary inversion-isometry lemma.
6. The complex coarse factor pays its explicit norm `(1 + r)^M`.
7. Every PRE-VALIDATION module is compiled in Colab before promotion; the
   diagnostic gate is not permission to remove PRE-VALIDATION.
8. This work does not move `20/41`, does not instantiate `TermSource`, and
   does not declare window 15 attained.

## Prepared diagnostic boundary

The first Eq. (3.37) Ubar-radius gate has one tracked prerequisite pair in
addition to its seven scratch pairs.  It must compile and audit all `26`
declarations of
`BalabanCMP99Eq337PhysicalComplexPerturbedBackground` before auditing the
`53` declarations in the scratch Ubar boundary.  A successful package thus
contains exactly `79` readouts.  The same evidence first seals only that
tracked source/audit pair and imports its audit into `YangMillsCore`; only
then may the fourteen scratch files be promoted, still visibly
PRE-VALIDATION, for the later prerequisite gate.  Materializing the tracked
source without auditing it is not a promotion precondition.

The next compiler-facing unit is intentionally smaller than the forced
recursion.  After the fourteen-file Eq. (3.37) Ubar boundary has been promoted
from its own cold evidence, the generator
`generate_eq337_complex_forced_recursion_prereq_runner.py` freezes a
stop-on-first-error Colab queue with this order:

1. the two-declaration Mathlib-only closed-radius scalar reproduction;
2. the Mathlib-only inverse-radius reproduction;
3. the project inverse-radius theorem and its one-declaration axiom audit;
4. the complex all-orientation small-field producer and its thirteen-declaration
   axiom audit.

The matching notebook generator gives the launcher a stable cell id and pins
the raw runner by commit and SHA-256.  A green diagnostic is evidence only for
these prerequisites; it does not authorize stacking or promoting the final
forced recursion, and it leaves `20/41`, `TermSource = 0`, and window 15
unchanged.

Promotion is deliberately split but evidence-bound.  After the first `79`
readouts, the tracked perturbed-background pair is sealed and its audit enters
`YangMillsCore`; the fourteen Ubar files are copied to their public paths while
retaining `PRE-VALIDATION`.  After the second gate's exact `16` readouts, the
single atomic helper
`seal_promote_eq337_complex_recursion_prerequisites.py` checks the promoted
Ubar blobs against the first package, checks the inverse/small-field scratch
blobs against the second package, removes the fourteen remaining notices,
promotes the four later files, and adds exactly nine audit imports to
`YangMillsCore`.  The Mathlib-only reproductions are never promoted.  Neither
package alone authorizes that final prerequisite seal.

The prerequisite boundary now also contains
`exists_cmp99SourceComplexUbar_zero_step_gates`.  It proves at radius zero,
with one common no-winding budget, the strict logarithmic gate, the strict
positive-link gate, and exact zero all-orientation successor radius.  This is
the required non-vacuity witness for the scalar interface; it does not weaken
or replace the flowing physical gates at nonzero radius.  The exact audit
scope is therefore sixteen declarations in total: two closed-radius scalar
declarations, one inverse-radius declaration and thirteen small-field
declarations.
