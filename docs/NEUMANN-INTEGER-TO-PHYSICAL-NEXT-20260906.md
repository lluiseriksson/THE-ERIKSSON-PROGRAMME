# Next R2 bridge after the seven-name integer image cold gate

Design only; no compiled result or counter movement. Do not turn a common
image-indicator equality into a physical inverse by renaming its parameters.

1. Define the canonical integer representative of a finite site by
   `fun mu => ((x mu).val : Int)` and prove injectivity coordinatewise.
   This is the same representative already used in the inverse direction of
   `cmp89SourceNeumannRectangleSiteEquiv`, not a chosen site dictionary.
2. Prove its exact compatibility with `cmp99GeneratedTerminalBlockSite`:
   the integer representative of the generated owner equals
   `neumannIntegerBlockOwner ((M^depth : Nat) : Int)` of the fine
   representative. The actual generated owner definition in
   `BalabanCMP99SourceGeneratedMassRange.lean` divides natural values by
   `M^depth`; Lean4 v4.29.0-rc6 `Init/Data/Int/DivMod/Basic.lean:120`
   supplies `Int.natCast_ediv`, with proof `rfl`. No real cast or rounded
   physical coordinate is involved. The existing one-block collapse remains
   a named alternative bridge, not an additional assumption.
3. Use injectivity plus that identity to transport owner-equality iff.
   Then consume the literal
   `cmp99SourceIteratedLift_flatExplicitCountingMass_single_apply` to express
   the actual generated counting-adjoint mass in integer-owner form. Keep
   `(cmp99SourceBlockAverageWeight M d)^(2*depth)` unchanged; do not replace
   it by the source-weighted coefficient to the power `depth`.
4. Specialize to the actual coarse region
   `cmp89SourceNeumannRectangleActiveRegion m`, with `hm` and `hfit` visible.
   Its lifted fine sides are `((M^depth : Nat) : Int) * m(mu)` by the sealed
   `cmp99IteratedLiftActiveRegion_cmp89Rectangle_eq`. A common printed image
   acts on integer representatives, not on an alleged permutation of the
   original half-open region. The source and target use the SAME `(k,branch)`.
5. Only then formulate the averaging intertwiner needed by the image sum.
   Fixed-image injectivity is not disjointness of the full image family and
   is not a summation interchange theorem. Those obligations must be proved
   separately before a right-inverse identity is claimed.

R1 literal regional precision/spacing/rectangle, R3 internally constructed
full fine-to-fine inverse, and R4 uniform physical value/derivative B0 remain
open. No compressed-Dirichlet/Neumann identification is imported.
20/41; TermSource0; window15 compatible and not attained.
