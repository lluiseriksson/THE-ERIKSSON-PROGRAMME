# Step 8b.24 C6c.3 source-sign gate

Status: static only; no `.olean`, focal, audit, root, or oracle verdict.

## Primary-source orientation

Visual inspection of CMP96 printed p. 229 fixes the convention before the
rescaled display (2.40):

* (2.38) is `Delta'_a G'_0 = I - sum K(h_box) G'(box) h_box`;
* (2.39) defines the middle species inside `K(h)` as
  `-(Delta h)(x) lambda(x)`.

Visual inspection of CMP96 printed p. 225 additionally fixes that `Delta` is
positive and that `Delta'_a = Delta + Q'^* a Q'`.  Thus the minus sign cannot
be discharged by silently switching to a negative-Laplacian convention.

The tracked positive-`D^*D` product rule instead has
`Delta_U(h phi) = h Delta_U(phi) - linkDerivative + cutoffLaplacian`.
This is consistent: the positive cutoff correction is the contribution of
`-K(h)` in (2.38), and the literal middle species *inside* `K(h)` is its
negative.  C6c.3 must state this sign dictionary explicitly.

The sealed theorem
`cmp99SourceGeneratedPhysicalPrecision_cutoffCommutator_apply_eq` independently
confirms the same tree convention: the full generated commutator is
`linkDerivative - cutoffLaplacianCorrection + generatedMassCommutator`.

## Quantitative substrate

The sealed producer to reuse is
`BalabanCMP99SourceSeparatedSignedCutoffLaplacian`, not the older
`BalabanCMP96Eq240SourceSeparatedCutoffLaplacian` bound:

* the signed tensor second difference has budget
  `48 * secondDerivBound / cutoffScale^2`;
* multiplying by the generated range squared gives
  `12 * secondDerivBound / K^2`;
* at unit rescaled spacing its coefficient acts exactly as
  `cmp99CutoffLaplacianCorrection`.

The older CMP96 module bounds eight first differences and therefore exposes
only `O(cutoffScale^-1)`.  It remains valid algebra but is not the C6c.3
producer described by the current frontier.

## Acceptance gate

A promoted C6c.3 pair must prove, rather than document:

1. the literal source middle species equals the negative of the positive
   `cmp99CutoffLaplacianCorrection` at rescaled unit spacing;
2. its pointwise action is bounded by
   `(48 * secondDerivBound / cutoffScale^2) * norm(phi x)`;
3. the range-squared normalization is exactly `12 / K^2`;
4. no Green estimate, cell/layer sum, local defect, contraction, or window-15
   attainment is claimed.

The scratch Lean pair beside this note freezes the intended declarations but
is not compiler-verified and is not promotable until its prerequisite queue is
sealed in order.

## Frozen scratch preview

The read-only preview and its synthetic fail-closed test currently report:

```text
STEP8B24_C6C3_PROMOTION_PREVIEW_OK files=2 declarations=4 audit_readouts=4 manifest_sha256=433678C571C602B9305AC937C05E712D2112C36A098DA508329F6DB43EE40958
STEP8B24_C6C3_PROMOTION_PREVIEW_SELFTEST_OK positive=pass source_tamper=fail_closed audit_scope=fail_closed missing_prerequisite=fail_closed target_collision=fail_closed
LEAN_OVERLAY_TEXT_OK files=2 source=paths:tmp/C6C3-SCRATCH-PATHS.txt
```

Frozen SHA-256 values:

```text
4A1B92B8D55AB28C47F9EAE483CF46B8FF09A6CF892BD8887956F1BEFD41A52D  tmp/BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacian.lean
A7D9438FAD9D637B6C56D7492EA2231A7883A6F71C149D5B6CEB58DF79650805  tmp/BalabanCMP96Eq240SourceSeparatedSignedCutoffLaplacianAudit.lean
EDD2BAE9A501100BD3E0AD330BBB73B0BEB57EFA199798C72AB8129BF3CFA860  tmp/audit_step8b24_c6c3_promotion_preview.py
C45012647AAEA3F9613FD2CC083FB5020CEC509B423B80FA8C64B7B4817F27DD  tmp/test_step8b24_c6c3_promotion_preview.py
```
