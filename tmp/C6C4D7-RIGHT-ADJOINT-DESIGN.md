# C6c.4d7 right-adjoint design (static; not evidence)

Target: the per-depth source-facing CMP99 (3.42) action for
`G'.comp D*`, with source owners on physical bonds and target owners on
active sites.

The abstract implication from the sealed `D G'` action by adjunction is not
valid: adjunction changes the blocks acting on the same vector.  Use the
literal physical backward divergence instead.

For a bond field `f` supported in one bond-owner fibre `owner`, put
`g = D* f`.

1. The backward-divergence stencil gives
   `supNorm g <= 8 / (ell * spacing) * supNorm f` in dimension four.
2. The same stencil proves exact owner support:
   the site-owner of every nonzero coordinate of `g` has
   `finBoxDist middleOwner owner <= 1`.
3. Decompose `g` exactly as the sum of `finitePiLpOwnerPart` over site owners.
   All owners outside that radius-one ball vanish before any norm estimate.
4. Apply the C6c.4d5 value-action theorem separately to every surviving
   owner part.  The finite supremum norm of an owner projection is no larger
   than the full supremum norm.
5. Compare the middle-owner decay to the requested source owner using the
   triangle inequality; this costs one `exp ownerRate`.
6. Bound the radius-one owner ball by the existing
   `finBoxDist_ball_card_le_two_mul_add_one_pow`; in dimension four this is
   `3^4 = 81`.  This is an owner-block constant, not a fine-fibre
   cardinality.

The resulting safe normalized amplitude is
`648 * ownerAmplitude * exp(ownerRate) / spacing`, multiplying the printed
`ell`.  A sharper five-owner enumeration can be considered later, but is not
needed for correctness.  Uniform physical `B0`/`delta0` remains a separate
analytic step.

## Prepared static split

Two draft files now isolate the elaboration boundaries:

* `BalabanCMP99ActiveRegionSourceCovariantAdjointStencil.draft.lean` proves
  the literal regional backward-divergence formula, its `2d/spacing`
  finite-supremum bound, and radius-one owner support.  Its proof uses the
  already sealed restriction/zero-extension adjunction and the explicit
  `gaugeConstraintQCLM_apply_background` stencil; it does not use Green
  symmetry.
* `FinitePiLpBlockLocalizedSupOwnerKernelComposition.draft.lean` converts a
  block-localized left factor plus an explicit right owner coefficient into
  a localized composition once the literal coefficient convolution is
  bounded.  The physical radius/cardinality estimate is deliberately not an
  input hidden inside this generic lemma.

The final physical brick will use the coefficient

`if finBoxDist middle source <= 1 then 8 / (ell * spacing) else 0`

and prove the convolution bound with the literal radius-one owner ball.
`finBoxDist_ball_card_le_two_mul_add_one_pow source 1` gives at most
`3^4 = 81` owners.  Multiplying `81 * 8` is the visible source of `648`;
no fine-site or fibre cardinality is allowed to enter.
