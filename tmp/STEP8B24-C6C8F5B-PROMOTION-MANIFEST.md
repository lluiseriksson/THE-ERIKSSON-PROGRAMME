# Step 8b.24 / C6c.8f5b PRE-VALIDATION promotion manifest

Status: **scratch only; not compiler-verified**.

## New files

| eventual tracked path | scratch source | SHA-256 |
|---|---|---|
| `YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion.lean` | `tmp/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegion.draft.lean` | `766A608169D73E3A95FB433A672AA4B480F5794BF896310283BC9D22D3F9D589` |
| `YangMills/RG/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegionAudit.lean` | `tmp/BalabanCMP99Eq335PhysicalLocalizedRetainedTowerOfSourceRegionAudit.draft.lean` | `3A43F4DB35A374160B9AADF37913CF29B1E9547DC1B9A94FA10D25DCAF40BD0D` |

The two-file scratch path list has SHA-256
`B7AB637FE6A3FD5E018A4CD133EB08E22513B5F651332CA82BA1A7A80A8D990D`.

The complete dependency closure through f5b contains twenty source/audit
pairs (forty files) in
`tmp/C6C8F5B-FULL-SCRATCH-PATHS.txt`, SHA-256
`BC82023D89DB02FE398748944D5BB7DE28722EC157846AAC5BA76FC52F2E1277`.
The canonical aggregate of the forty raw scratch blobs is
`15480683C94A3E6AF095DA53B3AD1EC197E444FE706C95ADD3DA38E0882E7008`;
the corresponding LF-normalized promoted-path manifest is
`7BB90E48BB18EBFE8777F24D5CBEBA71E3B1B980B7E6AAD137207F73E35D1B29`.
The lightweight gates report:

```text
LEAN_OVERLAY_TEXT_OK files=40
LEAN_IMPORT_PREFIX_OK files=40
PRE_VALIDATION_MARKERS_OK files=40 exact_count=1
```

These are textual gates only.  The existing audits contain 95 intended axiom
readouts across the full closure; source declaration-line counts are not an
equality gate because the prefix contains private/definitional helpers and
audits of generated structure projections.

The fail-closed read-only promotion preview and its synthetic self-test are
frozen at:

```text
A8A6B890DDE6D5DC6E6688285A70398707E2598337B05F88F84A462A32257EAF  tmp/audit_step8b24_c6c8f5b_promotion_preview.py
5E481E53BEE89FCF0CDE5B6B5E1C831226A2620CB7F3F1D5CA6E68465E69613D  tmp/test_step8b24_c6c8f5b_promotion_preview.py
```

Their current outputs are:

```text
STEP8B24_C6C8F5B_PROMOTION_PREVIEW_OK files=40 new_declarations=2 new_audit_readouts=2 manifest_sha256=7BB90E48BB18EBFE8777F24D5CBEBA71E3B1B980B7E6AAD137207F73E35D1B29
STEP8B24_C6C8F5B_PROMOTION_SELFTEST_OK positive=pass raw_tamper=fail_closed path_tamper=fail_closed semantic_tamper=fail_closed audit_scope=fail_closed marker_scope=fail_closed target_collision=fail_closed
```

This instrumentation writes no tracked file and is not compiler evidence.

## Design references

```text
C6c.8 design-map SHA-256:
43D5534197DF017E8539FF9EC4283B58CB14AE4D4E201838AB15B72E7E564F45

f2g containment-design SHA-256:
13F814F73B7AF213653641B2B2137B9975B078EF7360B4E31FE856AD9A3CD5B8
```

## Contract

- The public wrapper accepts the printed source-region dictionary, not the
  intermediate retained-carrier/cube inclusion.
- f2g.5 derives that inclusion internally from the recursive two-endpoint
  theorem and `OmegaPrime0.sites subset regular cube`.
- f5a then constructs the retained localized/canonical prefix and its
  terminal `Qprime` equality from the literal transformed background.
- No `fineSmall`, exterior extension, tower, prefix equality, Green or action
  bound is supplied by the caller.
- The forty-file closure deliberately excludes
  `BalabanCMP99SourceGaugeRegularGeneratedGreen`: that specialization uses the
  older Poincare-normalized generated mass and is not the source-faithful
  C6c.2/C6c.7 Green endpoint.  A later final specialization must instantiate
  the exact CMP85 prefix coefficient and identify its inverse through the
  inverse equations, never through a caller-supplied Green equality or
  `simpa` across the two coefficients.
- C6c.7 remains absent.  f5b is a geometric/source-dictionary closure, not
  Corollary 3.6 and not a terminal certificate producer.

## Validation order after Step8b22

The first sanctioned focal must materialize the entire forty-file closure and
verify every blob before compiling.  Stop on first error in this order:

1. retained endpoint geometry + its ten-readout audit;
2. source-region dictionary + its two-readout audit;
3. f5a retained prefix + its two-readout audit;
4. f5b source-region closure + its two-readout audit.

No root build, publication, PRE-VALIDATION removal or counter movement follows
from this static manifest.  The f5b pair may be sealed only after every
transitive scratch prerequisite used by that run has a compiler and axiom
verdict in the same prepared overlay.
