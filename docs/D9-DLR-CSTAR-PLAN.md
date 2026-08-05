# D-9 campaign: DLR, uniform completion, and the parameter frontier

Status: the contractive/completion core of A and the C-star part of B are
implemented; the optional nonconstant zero-coupling witness from A is not.
Stage C has the finite-system finite-set kernel, Markov projection, and exact
Gibbs tower identity.  Infinite-volume DLR passage, completed-state covariance,
stages D and E remain open and are not claimed by the present source.

Source base: `5cab0ba273f9b0d19abfb1ed8e64087919e4488c`.

## Target

Upgrade the D-8 positive normalized translation-invariant real functional on
the intrinsic local-cylinder quotient in three mathematically separate
directions:

1. an algebraic DLR specification for every finite site set, together with
   the DLR fixed-point identity for the constructed infinite-volume state;
2. a complex local star algebra with the uniform norm, its closed
   commutative C-star completion, and a norm-one positive extension of the
   state;
3. a sharper parameter producer based on the exact finite set of attainable
   local fields, separated from the classical envelope
   `2*tanh|beta| + 2*tanh|gamma|`.

No stage may use the thermodynamic-limit conclusion, DLR identity, or state
extension as an input to the theorem that is meant to establish it.

## Brick ladder

### A. Real algebra and contractivity

- Bundle the already-descended pointwise operations as a commutative real
  algebra; prove the realization map is an injective algebra morphism.
- Define the intrinsic uniform bound of a finite presentation and prove it is
  invariant under equivalent presentations.
- Prove directly from positivity and normalization that
  `|omega(F)| <= ||F||_infinity`.
- Supply a nonconstant one-site indicator attaining norm and state bounds in
  the zero-coupling model.

This stage is load-bearing for continuity. Merely adding typeclass instances
does not count as the campaign result.

### B. Complex local star algebra and C-star closure

- Complexify local cylinders without identifying the imaginary component by
  fiat: equality is equality of the represented complex global function.
- Prove pointwise conjugation, the star laws, the uniform C-star identity, and
  the isometric embedding into bounded continuous functions on the product
  configuration space.
- Define the quasi-local algebra as the topological closure of the local
  complex star subalgebra. The ambient closed-subalgebra instance, not an
  asserted completeness field, must supply the C-star structure.
- Extend `omega(F + iG) = omega(F) + i*omega(G)` continuously to the closure;
  prove normalization, positivity on `a^*a`, norm one, and full `Z^2`
  invariance.

Implemented except for the final completed-state `Z^2` invariance theorem.
The dense local algebra still inherits the fully invariant real state from
D-8; continuity of the translation automorphisms is the missing interface.

Death condition: if the extension is only postulated as a field or if the
domain is silently replaced by all continuous functions without a density or
closure proof, stage B is not closed.

### C. Finite-set DLR specification

- For a finite `Lambda subset Z^2` and an exterior configuration, define the
  finite conditional Ising kernel using exactly the bonds meeting `Lambda`.
- Prove positivity, normalization, measurability/locality at the cylinder
  level, preservation of constants, and specification consistency for nested
  finite sets.
- Prove the finite-volume tower identity whenever the conditioning set and
  the observable interaction neighbourhood lie inside the ambient volume.
- Pass that exact identity through the already-proved full-sequence limit to
  obtain `omega(gamma_Lambda F) = omega(F)` for every finite `Lambda` and
  local `F`.
- State uniqueness only after proving that any other DLR state in the same
  Dobrushin window agrees on every local cylinder.

Death condition: a structure carrying the DLR fixed-point equation as a
field, followed by a constructor that takes the same equation as a premise,
is packaging rather than a DLR theorem and does not count.

Implemented finite layer: arbitrary finite ambient site types and arbitrary
finite conditioning sets, with positive normalized exterior-local kernels,
preservation of constants, positivity, idempotence, and the exact Gibbs tower
identity proved by an involutive reindexing.  The infinite-lattice Ising
kernel and the passage of the identity through the thermodynamic limit remain
open, so the completed state is not yet labelled a DLR state.

### D. Geometry

- Generalize the finite-volume comparison producer from centred squares to
  arbitrary finite rectangles and translated rectangles first.
- Then isolate the exact boundary-defect hypothesis needed for a general
  exhaustion. A Følner theorem may be claimed only if the proof consumes the
  Følner boundary/volume condition and not merely cofinal containment.
- Record which boundary fields are covered; free/periodic equality is not a
  synonym for arbitrary one-body boundary conditions.

### E. Parameter frontier

- Define the exact horizontal and vertical influence coefficients by the
  finite supremum over attainable background fields of the anisotropic Ising
  star.
- Prove these coefficients dominate every rectangular finite-volume
  conditional and feed the comparison/telescoping chain.
- Exhibit a rationally certified parameter point where the exact-field row
  sum is below one while the envelope row sum is at least one, or report the
  attempted enlargement as negative evidence.

This remains a sharper Dobrushin-type region. It must not be called
"non-classical" merely because it improves the conservative envelope. A
genuinely beyond-Dobrushin region requires a different analytic mechanism
(for example a contour/cluster or exact-transfer argument) and a separate
campaign.

## Verification

All Lean/Lake work runs in fresh Colab Linux clones. Each green source anchor
requires:

```text
lake build <new terminal module>
lake build YangMillsCore
lake env lean oracle_check.lean
```

Every new headline is printed by the oracle and may depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Terminal reproduction means
two independent fresh Colab clones at the same SHA with matching log hashes.
Windows is used only for editing, Git, hashes, and previously measured light
checks.

## Claim boundary

Even successful completion of A--E would concern the two-dimensional lattice
Ising model. It would not provide an Osterwalder--Schrader reconstruction,
continuum limit, four-dimensional gauge theory, or Yang--Mills consequence.
