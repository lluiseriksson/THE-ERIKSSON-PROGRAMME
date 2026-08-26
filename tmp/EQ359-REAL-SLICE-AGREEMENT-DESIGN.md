# Eq. (3.59) real-slice agreement gate

Status: static design only.  No Lean/Lake or axiom verdict is claimed.  This
gate follows the fourteen-file Eq. (3.59) complex-tower promotion and precedes
the source-facing use of Eq. (3.60).  It moves neither `20/41` nor window 15.

## Why the gate is separate

`CMP99Eq359ComplexRegionalTowerPair` constructs the analytic forward and
printed-starred towers internally.  Its two differences are therefore honest
analytic objects:

```text
F2     = Q1 - Q0
F2star = starred1 - starred0.
```

That construction does not yet identify the compact real slice with the
sealed physical retained tower used by the literal Eq. (3.35) precision.
The complex `starred` recursion is an inverse-algebraic synthesis, while the
physical presentation is written with the real Hilbert adjoint.  Their
agreement on compact backgrounds must be proved; it cannot be inferred from
the agreement of the forward maps or from a generic `.adjoint` identity.

## Finite proof ladder

1. **Compact-to-complex group embedding.** Construct the canonical map from
   the physical `SUN Nc` matrix to
   `Matrix.SpecialLinearGroup (Fin Nc) ℂ`, and prove equality of the
   underlying matrices, products and inverses.  No arbitrary `SL` lift is an
   input.
2. **One-link forward action.** For a compact link `g` and real coordinate
   `X`, prove that `cmp99SpecialLinearAdjointCoordLM` at the embedded `g`
   applied to `cmp99SUNLieCoordComplexificationLM Nc X` equals the
   complexification of `matrixSUNAdjointModel Nc` applied to `X`.
3. **One-link printed star.** Prove the corresponding statement for inverse
   algebraic transport.  This is the real-slice theorem that justifies the
   starred synthesis; it must not be replaced by a theorem about norms.
4. **One-scale average.** Pointwise complexification commutes with the exact
   `M^{-d}` finite sum in `cmp99ComplexAdjointBlockAverageCLM` and the physical
   source-weighted block average.
5. **One-scale synthesis.** Pointwise complexification commutes with
   `cmp99ComplexAdjointBlockStarSynthesisCLM` and the physical weighted
   synthesis.  The unit synthesis mass and the physical `M^d` adjoint
   convention must be kept visible in this comparison.
6. **Tower induction.** Induct over the same
   `CMP99SourceActiveRegionChain`.  The baseline and perturbed analytic towers
   must be compared to the corresponding physical towers on identical typed
   carriers; no equality of terminal spaces or towers is caller data.
7. **Eq. (3.59) real slice.** Conclude that analytic `F2` restricts to the
   literal physical `Q1-Q0`, and analytic `F2star` restricts to the physical
   starred coefficient.  Only after this theorem may the complex Eq. (3.60)
   algebra be connected to the real precision producer.

## Acceptance checks

- The public theorem constructs or cites the compact-to-complex embedding by
  name; it does not accept a matrix equality as a hypothesis.
- Both forward and starred agreements are proved.  Forward agreement alone
  is insufficient.
- All sums use the already fixed `M^{-d}` forward mass and unit synthesis
  mass; no unnamed common constant is introduced.
- The induction consumes one shared region chain and the internally generated
  baseline/perturbed backgrounds.
- No finished Eq. (3.60) identity, inverse, `B0`, `delta0`, four-action bound
  or `norm R' < 1` appears as an input.

The next compiler-facing implementation should be split at the one-link and
one-scale boundaries so Mathlib elaboration failures can be reproduced
without rebuilding the full tower.
