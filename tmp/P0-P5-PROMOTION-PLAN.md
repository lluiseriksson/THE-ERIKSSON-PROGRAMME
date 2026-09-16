# P0--P9 promotion plan (static; not compiler evidence)

Status: planning only.  Step 8b.22 is cold-sealed, but the exact P0--P9
scratch checkpoint remains compiler-unverified.  Nothing in `tmp/` is
counted, sealed, promoted, or eligible for removal of `PRE-VALIDATION` until
that sequential gate is green.

## Exact source mapping

| Scratch source | Proposed tracked module |
|---|---|
| `P0CanonicalPrefixTower.lean` | `YangMills/RG/BalabanCMP99SourceCanonicalPrefixTower.lean` |
| `P1CoefficientMonotonicity.lean` | `YangMills/RG/BalabanCMP99SourcePrefixPoincare.lean` |
| `P2SourceCoefficientCoercivity.lean` | `YangMills/RG/BalabanCMP85SourcePrefixGreen.lean` |
| `P2bEffectiveQuadratic.lean` | `YangMills/RG/BalabanCMP85Eq221EffectiveQuadratic.lean` |
| `P2cCoarseCovariance.lean` | `YangMills/RG/BalabanCMP85Eq230CoarseCovariance.lean` |
| `P3ScalarRecurrence.lean` | `YangMills/RG/BalabanCMP85ScalarRecurrence.lean` |
| `P3BlockGaussianAlgebra.lean` | `YangMills/RG/BalabanCMP85BlockGaussianAlgebra.lean` |
| `P3TypedSchurBrackets.lean` | `YangMills/RG/BalabanCMP85TypedSchurBrackets.lean` |
| `P3TypedGreenInverse.lean` | `YangMills/RG/BalabanCMP85TypedGreenInverse.lean` |
| `P3SourceStepCoisometry.lean` | `YangMills/RG/BalabanCMP85SourceStepCoisometry.lean` |
| `P3PhysicalScalarSpecialization.lean` | `YangMills/RG/BalabanCMP85PhysicalScalarSpecialization.lean` |
| `P3PhysicalOperatorDictionary.lean` | `YangMills/RG/BalabanCMP85PhysicalOperatorDictionary.lean` |
| `P3PhysicalGreenRecurrence.lean` | `YangMills/RG/BalabanCMP85Eq241Eq242PhysicalGreenRecurrence.lean` |
| `P4aPhysicalBase.lean` | `YangMills/RG/BalabanCMP85Eq230BaseCovariance.lean` |
| `P4bFiniteTelescoping.lean` | `YangMills/RG/BalabanCMP85Eq243PhysicalGreenScaleSum.lean` |
| `P5PhysicalGreenScaleDictionary.lean` | `YangMills/RG/BalabanCMP89Eq234PhysicalGreenScaleDictionary.lean` |
| `P7SourceSeparatedAmbientPrefixPrecision.lean` | `YangMills/RG/BalabanCMP99SourceSeparatedAmbientPrefixPrecision.lean` |
| `P8SourceSeparatedRegionalPrefixGreen.lean` | `YangMills/RG/BalabanCMP96SourceSeparatedRegionalPrefixGreen.lean` |
| `P9SourceSeparatedPrefixCombesThomas.lean` | `YangMills/RG/BalabanCMP99SourceSeparatedPrefixCombesThomas.lean` |

Every promoted source receives a sibling `...Audit.lean`.  Scratch siblings
now cover every public declaration in P0--P2c, all seven P3 support modules,
the P3 physical endpoint, P4a, P4b, P5 and P7--P9.  The distinct
`P3PhysicalGreenRecurrenceAggregateAudit.lean` is retained as an additional
18-readout gate for the complete recurrence chain; it is not counted as the
three-readout sibling audit of the endpoint.

## Mechanical import rewrite

Rewrite only the `tmp.*` edge at the head of each file.  The dependency chain
is linear through P0--P4b; P5 additionally retains the two existing tracked
imports for the separated ambient dictionary and kernel-reindex algebra.
Audit siblings import their promoted source module.  No tracked source import
is replaced by a broader root import.

## Name hygiene

Promotion must remove the provisional `scratch_` / `Scratch` prefixes in one
mechanical pass over this closed dependency set, followed by an exact
collision audit against `YangMills/**`.  The pass may change identifiers and
their internal references only; theorem statements and proof terms remain
byte-equivalent modulo those names and import paths.  A collision is resolved
by a source-specific CMP85/CMP99 name, never by weakening or overloading a
tracked declaration.

## Validation sequence

1. Preserve the independently sealed Step 8b.22 evidence.  Do not mix its
   evidence or source checkpoint with P0--P5, and require a green sequential
   P0--P9 scratch gate before creating the first promoted source checkpoint.
2. Create one PRE-VALIDATION checkpoint containing the promoted P0 source and
   sibling audit only.  Run a warm Colab diagnostic against the exact SHA and
   stop on the first elaboration or axiom error.
3. Advance in dependency order, one first-error diagnostic at a time.  A
   downstream file is not introduced into the diagnostic queue until its
   predecessor source and audit are green in the same disposable Colab
   checkout/cache generation.
4. Keep the P2b/P2c boundary and the generic/physical P3 boundary explicit.
   No caller-supplied Green family, recurrence, inverse equality, tower
   equality, or zero-control conclusion is an admissible repair.
5. After the complete P0--P9 queue is warm-green, create one prepared terminal
   checkpoint and run exactly one cold validation for that checkpoint.  The
   seal requires exact source SHA, toolchain and Mathlib pins, real focal and
   audit exit codes, expected axiom-header counts, and durable evidence.
6. Only a later seal commit may remove PRE-VALIDATION from modules certified
   by that cold run, add their core imports, and update the ledger/map.

## P7--P9 boundary

P7 fixes the zero-bare-mass, final-positive-prefix precision and transports
its coercivity and inverse laws onto the exact separated ambient carrier.
P8 constructs the finite-range-thickened Dirichlet region and its canonical
regional inverse.  P9 derives per-depth Combes--Thomas kernel bounds for that
same precision/Green pair.  Promotion must keep their source-visible inputs
unchanged: the one terminal Poincare absorption inequality remains visible,
and P9 must continue to state explicitly that it does not produce a uniform
CMP99 (3.42) pair, the four localized source actions, C6c.4, or window 15.

No promoted P7--P9 declaration may accept a precision, Green, inverse law,
coercivity witness, regional action estimate, or decay conclusion from the
caller.  Their `scratch_` prefixes are removed only mechanically across this
closed dependency suffix.

## Counter boundary

P0--P9 close the source-specific prefix Green reconstruction through CMP89
(2.34), its regional Dirichlet inverse, and per-depth Combes--Thomas bounds.
They do not construct the CMP96 Dirichlet defect, random-walk closure,
uniform CMP99 (3.42) constants, the four-action regional certificate, window 15, any additional
`PreEq136` producer, or a `TermSource`.  Therefore their static preparation
and even their eventual isolated seal do not by themselves change `20/41`,
`TermSource = 0`, or "window 15 compatible but not attained".

## No-renaming audit of the two smallness inputs

The two hypotheses carried through P0--P5 have different status and must not
be conflated.

* `fineSmall` is the all-oriented-edge estimate

  ```lean
  ∀ e, ‖(background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon.
  ```

  It is a legitimate internal parameter of the generic retained-tower
  machinery.  It is not an additional physical input: for a
  `PhysicalGaugeBackground`, the already tracked and axiom-audited theorem
  `norm_physicalGaugeBackground_apply_sub_one_le` derives it from the single
  positive-bond premise `PhysicalWilsonSmallBackground background epsilon`,
  using the orientation law and unitarity with no loss in the constant.
  `CMP99SourceUbarClosedBudget` deliberately does not contain this field; it
  controls only the scalar radius/no-winding chain.

  Consequently, promotion of the low-level P0--P5 chain may retain
  `fineSmall`, but no terminal/source-facing claim may count it as an open
  analytic obligation.  The later CMP116 physical wrapper must construct it
  internally from `PhysicalWilsonSmallBackground`.  P5 must not import the
  CMP102 bridge backwards merely to hide the parameter: that would invert the
  source-layer dependency.  Until the higher wrapper is present, P5 is a
  technical Eq. (2.34) dictionary endpoint, not a complete physical producer.

* `hsmall : cmp99SourcePoincareErrorCoeff ... < 1` is different.  It is the
  terminal Poincare absorption inequality and remains an explicit scalar
  reachability obligation.  P1 proves that this one terminal inequality
  supplies every prefix; it does not prove the terminal inequality itself.
  The scratch positive-radius theorem shows compatibility/non-vacuity, but it
  is outside this promotion set and is not compiler evidence for P0--P5.

Thus this audit introduces no extra physical premise and removes none by
renaming: the all-edge bound is derivable at the higher physical boundary,
whereas the Poincare contraction remains visible until its own producer is
promoted and sealed.

## P5 endpoint input ledger

The final P5 theorem
`cmp89SourceSeparatedAmbientGreenScaleSum_eq234` (provisional scratch prefix
omitted here) has no caller-supplied Green, covariance, increment, recurrence,
inverse, reindexing equality, or scale-sum identity.  Its public inputs have
the following exact status.

| Input | Status at the physical boundary |
|---|---|
| `hL : 2 <= L` | printed RG-ratio regime; geometric/scalar datum |
| `depth`, `K`, `Q`, `Nc` and `NeZero` instances | finite scale/carrier data; `K` remains distinct from `L` |
| `spacing > 0` | source lattice spacing; the later physical specialization must fix its intended normalization explicitly |
| `a > 0` | base CMP85 averaging coefficient, not a free per-scale family |
| `background` | literal full periodic `GaugeConfig ... (SUN Nc)` |
| `CMP99SourceUbarClosedBudget` | one closed scalar radius/no-winding budget |
| `fineSmall` | internal all-edge form; derived later from the one positive-bond physical premise, as audited above |
| `cmp99SourcePoincareErrorCoeff ... < 1` | the sole open terminal Poincare absorption inequality |

The apparently free `a` is not a renamed `a_j` family.  P2 defines the
prefix coefficient internally as

```lean
cmp99SourceMassParameter a (M : real) (r.val - 1)
```

and uses its tracked recurrence and positivity.  Thus the whole scale family
is constructed from one positive base coefficient.  The hRpoly consumer must
still identify/fix that base coefficient and the spacing according to its
source normalization, but it must not accept a family of scale coefficients.

With those two later specializations and the physical discharge of
`fineSmall`, the only analytic premise surviving this P0--P5 chain is the
named terminal Poincare absorption inequality.  This statement is a static
signature audit only; it does not promote or compiler-verify any scratch
module.

That physical discharge now has a separate, correctly layered scratch pair:

```text
P6CMP116PhysicalGreenScaleDictionary.lean
  B154E51AC47BE9D222F3EDEED1DC2FCBB4328B3BC87F843A7C144652FD56704E
P6CMP116PhysicalGreenScaleDictionaryAudit.lean
  F459952E2EAFAD183D410922EFE442D473F77A222FCF48E29A60D641013C5DD1
```

It imports P5 from above and the already tracked
`norm_physicalGaugeBackground_apply_sub_one_le` producer from the physical
layer, constructs the all-oriented-edge bound internally from
`PhysicalWilsonSmallBackground`, and returns the exact P5 (2.34) equality.
Its source-facing endpoint also retains the literal coefficient and operator
order in the theorem conclusion.  It keeps
`cmp99SourcePoincareErrorCoeff ... < 1` visible.  The import direction
is intentional: no CMP102/CMP116 module is imported backwards into P0--P5.
The two-file path list has SHA-256
`B591C5714DC1BA79248D1A56AED655D00BD47954703E0CDE7EF027D86F5A5BF2`;
its exact two-row byte manifest has SHA-256
`51A1127D87914E176B71F9568DAF10D10BCE17F225FE6E146DCC8C254DA9C7CD`;
the text and import-prefix guards report `files=2`.  This remains unelaborated
PRE-VALIDATION scratch and is not part of the frozen 33-file P0--P5 closure.

## Mandatory coefficient/object identity gate after P5

P5's source-faithful CMP85 precision is not definitionally the older tracked
Poincare-normalized generated precision.

* P2--P5 generate the printed scale coefficient from one base `a` as
  `cmp99SourceMassParameter a (L : real) j`, together with the exact
  source-weighted/counting-Hilbert volume conversion.
* `cmp99SourceGeneratedPhysicalPrecision` instead uses
  `cmp99SourceGeneratedPhysicalMass d L depth spacing epsilon`, obtained by
  normalizing the recursively generated Poincare energy coefficient.  This
  scalar depends on the Poincare ledger (and in general on `epsilon`).

There is currently no tracked or scratch theorem equating these two scalars,
their precisions, or their inverse Green operators.  A repository-wide static
search found no declaration containing either orientation of such an
identity.  Therefore downstream work has exactly two honest routes:

1. use the new P5 source Green as the physical object consumed by the CMP96 /
   CMP99 reconstruction; or
2. prove an explicit source-backed scalar identity and then an operator
   dictionary before reusing the older generated physical Green.

Definitional identification, `simpa` across the two coefficients, or a
caller-supplied equality is forbidden.  Until one of the two routes is
completed and compiler-audited, P0--P5 close CMP85 (2.43) and its CMP89
(2.34) reindexing only; they do not identify that Green with the existing
Poincare-normalized physical Green used elsewhere in the tree.  This gate is
separate from the terminal Poincare absorption premise itself.

The depth-one scalar check already shows why no universal identification is
available.  After cancelling the positive one-scale Poincare constant, the
older generated mass at depth one is `spacing^(-2)`.  By the proved P2
counting/source-weight conversion, the first positive CMP85 prefix in four
dimensions has counting coefficient

```text
a * (L * spacing)^2 / spacing^4 = a * L^2 * spacing^(-2).
```

Equality would therefore force `a * L^2 = 1`; P5 correctly quantifies over an
arbitrary positive printed base coefficient `a`.  This calculation is a
static diagnostic, not a sealed Lean no-go, but it rules out treating the two
objects as universally definitionally equal.  The preferred source-faithful
route is consequently to carry the P5 Green forward; any alternative must
first state and prove the required parameter specialization explicitly.
