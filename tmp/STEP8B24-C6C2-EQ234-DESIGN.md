# Step 8b.24 C6c.2: source-faithful CMP89 (2.34) design

Status: static design only.  No Lean/Lake compilation has been run for this
artifact.  This file does not change a terminal counter and is not evidence
that C6c.2 exists.

## Printed identity

The primary CMP89 render, printed p. 582, gives the dimension-four identity

```text
G_k(Box)
  = C^(0),eta(Box)
    + sum_{j=1}^{k-1}
        a_j^2 * (L^j * eta)^(-4)
          * G_j^eta(Box) * Q_j^*
          * C^(j),L^j eta(Box)
          * Q_j * G_j^eta(Box).                         (2.34)
```

The same page immediately states that the right-hand side is built from the
operators `G_j^eta(Box) Q_j^*` and `C^(j),L^j eta(Box)`.  Lemma 2.4 then gives
the value/left-difference/Hölder/coarse-covariance estimates consumed after
this identity.

This is a **finite RG-scale sum**.  It is not a telescope over nested spatial
regions and it is not a sum of consecutive `Omega`-restriction defects.

## Printed one-step recurrence (the actual induction engine)

The primary lower-bound paper prints the exact predecessor of (2.34).  On
printed p. 612, Eq. (2.42) is

```text
G_(k+1)^eta(Omega,A)
  = G_k^eta(Omega,A)
    + a_k^2 * (L^k * eta)^(-4)
        * G_k^eta(Omega,A) * Q_k^*(A)
        * C^(k),L^k eta(Omega,A)
        * Q_k(A) * G_k^eta(Omega,A).                 (2.42)
```

The source then says to apply (2.42) recursively and uses
`G_1^eta = C^(0),eta`; the result is Eq. (2.43), which is the same finite
identity printed later as CMP89 (2.34).  Thus C6c.2 does not need to guess a
Woodbury-style split.  It must formalize this literal recurrence and then
perform finite induction.

Eq. (2.41), immediately above it, also fixes the normalization of the
averaged next Green.  It is a useful independent gate on the scalar factor
and adjoint orientation, but it is not a substitute for (2.42).

## Measured negative identifications

### The regional coarse-covariance telescope is not (2.34)

`BalabanCMP99SourceRegionalCoarseCovarianceTelescope.lean` proves

```text
sum_r (embeddedCoarseCovariance_(r+1) - embeddedCoarseCovariance_r)
  = embeddedCoarseCovariance_last - embeddedCoarseCovariance_zero.
```

Its index changes the regional carrier inside one fixed-scale construction.
It has no `a_j^2 * (L^j eta)^(-4)` weight, no `G_j Q_j^* C^(j) Q_j G_j`
summand and no RG-prefix index.  Reusing it as (2.34) would be a typed but
source-false identification.

### The generated terminal conditional covariance is not printed `C^(j)`

`cmp99SourceGeneratedPhysicalCoarseCovariance` is the inverse of

```text
Q_j * G_j^2 * Q_j^dagger.
```

It is the conditional-covariance middle used by the gauge projection.  The
primary CMP85 formulas instead define

```text
Delta^(j) = b_j I - b_j^2 Q_j G_j Q_j^dagger,       (2.21)
C^(j) = (a * spacing_(j+1)^(-2) P(A) + Delta^(j))^-1. (2.30)
```

These are different operators, not two presentations of the same middle.
No tracked theorem identifies them, and the conditional inverse may not be
used as the printed `C^(j)`.  Moreover the `P(A)` in (2.30) is the one-step
projector `Q_step(A_j)^dagger Q_step(A_j)` on the scale-`j` carrier, whereas
the projector in the fine precision is the prefix
`Q_j(A)^dagger Q_j(A)` on the original fine carrier.  Their types and roles
must remain separate.

### The retained stratified covariance still uses the wrong Green family

`CMP99SourceRetainedPhysicalScaleIdentification` canonically exposes every
retained `Q'_r` prefix and constructs a covariance on every source stratum.
However, `stratumCoarseCovarianceMiddle` uses the same complete
`I.green ...` for every `r`.  Printed (2.34) uses the RG-prefix family
`G_j^eta(Box)`.  Therefore the existing stratum family is useful carrier and
adjoint algebra, but is not definitionally the printed family.

### The retained tower exposes `Q_j`, but not the physical prefix Green

`CMP99SourceRetainedPhysicalTower` retains `towerAt`, `nextAverage`, the
level-site types and their canonical isometries.  It does not retain a public
family of physical prefix precisions or Greens.  This does **not** mean that
the public interface needs a second family of evolved backgrounds: the
printed `G_j(A)` acts on the original fine carrier and uses the original
covariant Laplacian together with the internally generated prefix
`Q_j(A)`.  The missing object is therefore the prefix precision

```text
Delta_A + a_j * spacing_j^(-2) * Q_j(A)^dagger Q_j(A)
```

and its internally constructed inverse, not a caller-supplied background
family.  The existing complete stratified precision sums all strata
simultaneously and is not this single-prefix precision.

## Reusable tracked substrate

The following pieces are real inputs to C6c.2.

1. `cmp99SourceGeneratedRetainedPhysicalTower` constructs every normalized
   `Q'_j` prefix from one physical `Ubar` recursion.
2. `CMP99SourceRetainedPhysicalTower.towerAt_succ_Qprime` proves the exact
   source order `Q'_(j+1) = Q_j(U_j) Q'_j`.
3. The retained scale identification gives the canonical dependent carrier
   and isometry at every level; no caller-chosen scale-site equivalence is
   needed.
4. `cmp99SourceEq325PhysicalGaugeComplement` already has the outer algebraic
   operator shape

   ```text
   G * Q'^dagger * C * Q' * G,
   ```

   but its `C` is the inverse of `Q_j G_j^2 Q_j^dagger`.  It is reusable only
   as composition syntax, not as the printed CMP85 covariance.
5. `CMP99SourceRetainedPhysicalScaleIdentification.physicalStratumCoarseCovariance`
   provides internally constructed conditional inverses and both inverse
   laws.  It does not provide CMP85 (2.30).
6. The running coefficient `a_j`, its uniform positive floor and the exact
   scale spacing `(M : R)^j * spacing` are already tracked separately.
7. `BalabanCMP99OneScalePhysicalGreenCovariance` already constructs, for one
   literal physical scale, the precision, its coercivity constant and its
   Green.  Its later `Q G^2 Q^dagger` inverse is again conditional and is only
   a proof template for inverse construction.
8. Generic finite-dimensional covariance/inverse machinery can construct an
   inverse once coercivity of the **literal** (2.30) precision is proved.  The
   missing Schur operator and its positive-definiteness proof remain new.

These ingredients remove the possibility of passing unrelated `Q_j`,
adjoints or coarse covariances.  They do not yet prove their assembly is the
printed RG identity.

A declaration search found no theorem asserting the printed equality

```text
G_(j+1) = G_j + a_j^2 * spacing_j^(-4) * Eq325Complement_j.
```

The existing generated coarse-covariance transition compares different
spatial `Omega` carriers and proves a rectangular resolvent identity.  It is
not the same scale recurrence and cannot discharge (2.42).

## Missing construction

C6c.2 must add a retained **physical RG-prefix Green package**, generated
from the existing retained `Q_j` recursion, with the following data produced
internally for every
`j : Fin k`:

1. the canonical retained prefix `Q_j(A)` on the original fine carrier;
2. the literal source coefficient `a_j` and its recurrence/positivity, with
   the sealed dictionary `source j >= 1 <-> Lean (j - 1)`;
3. the prefix precision
   `Delta_A + a_j spacing_j^(-2) Q_j(A)^dagger Q_j(A)` on that same
   carrier;
4. a coercivity proof for that literal prefix precision and its constructed
   Green `G_j`, with both inverse laws;
5. the exact Hilbert-adjoint/source-weighted-adjoint and scale-spacing
   dictionaries;
6. for source `j >= 1`, the effective operator
   `Delta^(j) = b_j I - b_j^2 Q_j G_j Q_j^dagger`, the literal coarse
   precision `a spacing_(j+1)^(-2) P(A) + Delta^(j)`, and its generated
   inverse `C^(j)`;
7. the transported fine-carrier summand

   ```text
   a_j^2 * spacing_j^(-4)
     * G_j * Q_j^dagger * C^(j) * Q_j * G_j;
   ```

8. the base fluctuation covariance `C^(0),eta` on the same fine carrier,
   constructed separately from (2.17)+(2.30), without inventing `G_0` or
   evaluating the positive-level Schur formula (2.21) at zero.

The package must be generated from the initial background, one existing
`CMP99SourceUbarRadiusChain`, the retained physical `Q_j` tower and the
source recurrence for `a_j`.  It may not accept a family of backgrounds,
Greens, covariances, carrier equivalences, coercivity certificates or inverse
equalities.  In particular, it must not substitute the complete stratified
precision of CMP99 (3.24), whose simultaneous sum over strata is a different
operator.

## Exact proof architecture

The finite equality should be proved as an induction on the physical RG
recursion, not as an extensional equality supplied by the caller.

### C6c.2a -- construct the physical prefix Green family

Use `cmp99SourceGeneratedRetainedPhysicalTower.towerAt j` as the unique
source of `Q_j(A)`.  On the original fine carrier, define the literal
prefix precision

```text
-Delta_A + m^2 * I
  + a_j * spacing_j^(-2) * Q_j(A)^dagger * Q_j(A)
```

with the bare physical mass `m` and the correctly shifted averaging
coefficient kept as distinct parameters, then construct its Green from a
generated coercivity theorem.  Source CMP85 has
`a_1 = a`, while Lean has
`cmp99SourceMassParameter a (Lblock : R) 0 = a`; hence source index `j >= 1` uses Lean
index `j - 1`.  The new family should retain
only the precision/Green/coarse-covariance values and their proved laws; it
must not create a parallel `Q_j` recursion or accept coercivity from the
caller.

The generic source-facing family retains `m`.  The hRpoly specialization
must set `m := 0` internally, matching the sealed flat physical-precision
dictionary.  The current tree already proves that its complexification is
`cmp99SourceFlatFullComplexPrecisionAction 0 A`; it does not contain an
unaccounted bare-mass summand.  `cmp99SourceMassParameter` is `a_j`, not `m`,
and `cmp99SourceGeneratedPhysicalMass` is another normalized `Q'^*Q'`
coefficient.  No one of these may discharge another by notation.

The quantitative subfrontier is therefore one theorem family: the absorbed
physical Poincare/coercivity estimate for every canonical `towerAt j` prefix.
The correct input is the chain-generic
`CMP99SourceActiveRegionChain.norm_sq_le_absorbed_poincare` applied to the P0
truncation, before its coefficients are normalized into a chosen terminal
mass.  The specialized `cmp99SourceIteratedLift_..._with_Qprime` public
signature reconstructs a depth-dependent fine lattice and is not valid for
an intermediate prefix that retains the original fine carrier.  From

```text
(1-B) * ||phi||^2 <= A * energy(phi) + C * ||Q_j phi||^2
```

and `b_j = a_j spacing_j^(-2) > 0`, the prefix precision receives the
explicit coercivity floor

```text
(1-B) * min(A^(-1), b_j * C^(-1)).
```

The exact algebraic normal form may differ, but both branches of this minimum
must remain visible.  Existing `cmp99OmegaSourcePhysicalOneStepGreen` is the
literal one-step endpoint.  By contrast,
`cmp99SourceGeneratedPhysicalGreen` uses
`cmp99SourceGeneratedPhysicalMass`, a Poincare-normalization quotient rather
than the source flow `a_j`; it is a proof template, not an Eq.-(2.42)
endpoint.  The complete retained precision is also different because it sums
all strata.  C6c.2a must lift the raw absorbed Poincare argument to every
retained prefix.  After constructing `G_j`, it must separately construct the
literal (2.21) effective operator and prove coercivity/injectivity of the
literal (2.30) coarse precision.  The inverse of `Q_j G_j^2 Q_j^dagger` is
not admissible as `C^(j)`.

The preferred implementation is a theorem/companion package generated from
the existing retained tower, not a new public field that lets callers attach
arbitrary coercivity certificates.  If extending the private retained
constructor is materially simpler, the new proof component must still be
filled only by `cmp99SourceGeneratedRetainedPhysicalTower`.

The typed bridge required before this theorem is now measured.  The active
region chain and the `Ubar` radius chain are both inductive from the fine end,
so each admits a canonical truncation to its first `r` steps.  Prove that
`towerAt r` equals `weightedQprimeTower` for those two truncated chains.  The
existing `towerAt (Fin.last depth)` bridge is precisely the terminal case.
This family theorem lets the tracked terminal absorbed-Poincare result apply
at every prefix without rewriting the fine lattice as a product involving
`depth-r`.

### C6c.2b -- exact physical Green recurrence (2.42)

On one generated scale, construct `G_j`, `G_(j+1)`, `Q_j` and the literal
`C^(j)` from the same retained physical recursion and prove Eq. (2.42) as an
operator equality.  The correction term may reuse generic composition
syntax, but it must use the inverse laws of the literal CMP85 (2.30)
precision, not the Eq.-(3.25) conditional middle.
No `G_next = ...`, recurrence equality or final splitting equality may be an
input.

The exact orientation and source spacing factor must be visible in this
brick.  In dimension four the public coefficient must normalize to
`a_j^2 * spacing_j^(-4)`; it must not be replaced by an unnamed positive
constant or by a counting-cardinality factor.

The proof obligation is now sharply separated into two parts:

1. an algebraic block-Gaussian calculation with
   `b_j = a_j spacing_j^(-2)`,
   `c_j = a spacing_(j+1)^(-2)` and
   `b_(j+1) = b_j*c_j/(b_j+c_j)`, identifying the generated next inverse
   with `G_j + coefficient * complement_j`;
2. the physical dictionary showing that the coefficient, average and
   weighted adjoint are exactly the source `a_j`, `Q_j(A)` and `Q_j^*(A)`.

The first part may be a generic theorem.  The second must be a theorem about
the internally generated physical level, not caller data.

### C6c.2c -- generated physical base

Before summing, prove the separate source identity printed immediately
before (2.43):

```text
G_1^eta(Omega,A) = C^(0),eta(Omega,A).
```

The primary formulas determine it rather than postulate it.  At the base,
`a_1=a`, `Q_1=Q_step`, (2.17) supplies the unaveraged quadratic operator,
and (2.20)/(2.30) give the same precision
`-Delta_A + m^2 + a*spacing_1^(-2)*Q_step^dagger*Q_step` on both sides.
The Lean coefficient is exactly
`cmp99SourceMassParameter a (Lblock : R) 0`.  The base brick must prove this
precision equality from the internally generated dictionaries, construct
the (2.30) inverse `C^(0)` separately, and conclude by uniqueness from the
two ordered inverse laws.  It may reuse the P2a coercivity/injectivity of the
equal precision, but it must not instantiate the positive-level (2.21)/P2c
package at zero.  A supplied base covariance, base equality, or precision
equality is rejected.

For the generic CMP85 theorem the displayed `m^2` is literal.  For the
hRpoly endpoint the base-equality theorem is separately specialized at
`m = 0`; this specialization is a named dictionary step, not a definitional
omission.  The already sealed mass-zero nonvanishing route is the relevant
analytic consumer, while the separate physical mass-flow window remains
outside this zero-mass endpoint.

### C6c.2d -- finite RG sum

Iterate the literal recurrence (2.42) over the retained physical recursion
and prove Eq. (2.43)/(CMP89 (2.34)), with indices corresponding to source
`j = 1,...,k-1`.  The base theorem must identify
`G_1^eta = C^(0),eta`; base and terminal off-by-one cases must be separate
theorems.  The result must live on one named fine carrier before any
CMP95/CMP96 localization transport.

The preferred public finite index is `Finset.Ico 1 k`.  It is empty at the
source base `k = 1` and contains exactly `1,...,k-1` otherwise.  A `Fin k`
sum would silently add the forbidden `j = 0` term; a `Fin (k-1)` family would
need an explicit `j = i+1` transport at every dependent carrier.  If the
implementation chooses either alternative, that shift must be a named
equality rather than hidden in simplification.

There are therefore **two** index shifts to keep separate:

1. the operator prefix `Q_j`/`G_j` has source order `j`;
2. the source coefficient `a_j` is
   `cmp99SourceMassParameter a (Lblock : R) (j-1)`.

The equality connecting those conventions must be stated once in the
physical dictionary.  Reusing the same Nat as both indices without that
theorem is rejected.

### C6c.2e -- CMP95/CMP96 carrier and scale transport

Transport the equality through the already named level isometries and the
fine/block spacing lemma.  This layer may change coordinates; it may not
change the operator family or absorb scale powers into an opaque constant.

## Acceptance gates

1. The public conclusion contains the literal finite sum and the literal
   `a_j^2 * spacing_j^(-4)` coefficient.
2. Every `G_j`, `Q_j`, weighted adjoint and `C^(j)` is generated from one
   retained physical `Q_j(A)` recursion and one literal source coefficient
   recurrence; no parallel tower or caller family is accepted.
   In particular `C^(j)` is the inverse of the (2.30) precision containing
   the (2.21) Schur operator, not the inverse of `Q_j G_j^2 Q_j^dagger`.
3. The `j`-th Green is a genuine prefix Green.  Reusing the final Green for
   every stratum is rejected.
4. The theorem identifies its base covariance `C^(0),eta`; it is not an
   arbitrary supplied endomorphism.
5. Both inverse laws used in the one-step split are derived internally.
6. No regional-`Omega` telescope is used as the RG-scale sum.
7. The source-weighted adjoint is used with the exact spacing ratio.  A bare
   Hilbert adjoint is accepted only after an explicit equality theorem.
8. No ambient-volume, source-cardinality or owner-count factor appears.
9. C6c.2 ends with an equality of operators, not merely equality on a chosen
   source or a norm bound.
10. The one-step theorem's left side is the internally generated
    `G_(j+1)`, and its first right summand is the internally generated `G_j`;
    a caller-supplied recurrence is rejected.
11. The finite theorem cites the base equality `G_1 = C^(0)` rather than
    choosing an arbitrary starting covariance.
    That equality is its own audited producer, derived from equality of the
    literal base precisions and inverse uniqueness.
12. The public summation index is proved extensionally equal to the printed
    range `1 <= j < k`; no `j = 0` or `j = k` term is present.
13. The source/Lean coefficient shift is visible:
    `a_1 = massParameter 0` and source `a_j = massParameter (j-1)`.
14. No theorem replaces `a_j` by `cmp99SourceGeneratedPhysicalMass`; that
    auxiliary mass belongs to a different normalized precision.
15. The source-facing package retains the bare scalar `m`; the hRpoly
    specialization fixes it to zero by the sealed physical-precision
    dictionary.  `m`, `a_j`, and `cmp99SourceGeneratedPhysicalMass` remain
    three distinct quantities in names and theorem signatures.
16. Completion of C6c.2 still does not construct the CMP96 regional Green:
    C6c.3--C6c.9 remain open and counters remain unchanged.
17. The printed RG factor `L` and the tracked tower's internally named `M`
    are one parameter in this package: instantiate the tower with
    `M := Lblock` and set `L_source = (Lblock : R)`.  No independent real `L`
    plus an equality hypothesis is accepted.
18. The independent regional large-block parameter `K` does not occur in
    P0--P4 and remains free downstream.  The old diagonal specialization
    `K = Lblock` is not reintroduced by this dictionary.

## Current verdict

The tree has the generic composition syntax for a `G Q^dagger C Q G`
operator and the canonical retained `Q'_j` prefixes, but the existing `C` is
the wrong conditional inverse for the printed recurrence.  The missing
object is not a generic telescope.  It is the source-faithful family of
prefix Greens, the literal (2.21) effective operators, the literal (2.30)
coarse covariances and the exact Green recurrence (2.42) tying them together.
Once that recurrence exists, (2.34) is finite induction; until then C6c.2
remains a genuine design boundary rather than composition work.
