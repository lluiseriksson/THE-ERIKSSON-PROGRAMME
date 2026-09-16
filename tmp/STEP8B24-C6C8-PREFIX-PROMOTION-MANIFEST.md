# Step 8b.24 C6c.8a--e prefix promotion manifest (source-faithful subset)

Status: PRE-VALIDATION / NOT PROMOTED / NOT COMPILER-VERIFIED.

This checkpoint must not be materialized in the tracked tree until the
currently running Step8b22 cold terminal job has emitted its final verdict
and its evidence has either been sealed or classified.  The current tracked
HEAD remains `b05ef65af97a95752d1c929e30749d886d425d8d`.

## Exact scratch inputs

```text
B320A7FDCDCC5DF3EBBC8C9D367A985ADC66C005461F8833DD3F08A027F12CD5  tmp/BalabanCMP99RegionalGaugeIsometry.draft.lean
023F177C753E19FA03A048A5A22C36083DF6CD8C824787362C523C8F77FF97EA  tmp/BalabanCMP99RegionalGaugeIsometryAudit.draft.lean
7518673956F06984846ED9147884B0DEBF065BC7F2BCA6CB1356EE04106B6D49  tmp/BalabanCMP99CovariantD0GaugeIntertwiner.draft.lean
C03B6EBF078C573CE8B136C657D16D2C9A0F1FAD76938C9FBA14AC913243A073  tmp/BalabanCMP99CovariantD0GaugeIntertwinerAudit.draft.lean
00BE5BA4DAC303068C82234B28F5997A54E9BE4594301A31B7EB67CD5AEDC71D  tmp/BalabanCMP99SourceGaugeDeviationTransport.draft.lean
6F16AA9302AD5F4EC9CE5491D89BA9C6409ECA2A3409DC278256456BAE62B0DB  tmp/BalabanCMP99SourceGaugeDeviationTransportAudit.draft.lean
7B0CD9A2F294D3A389837182B7A2D56BB34A03F288E6F44BBBDF2785157B5944  tmp/BalabanCMP99SourceGaugeRegularScalePair.draft.lean
4B3683983EEB0BBF9B1CF09C7933BAE6560E9960C4DEA7CEC63769186EF95A5C  tmp/BalabanCMP99SourceGaugeRegularScalePairAudit.draft.lean
A84FB1853B018834FCD2573BEFC29938C9EE839408D53F6ECA3CB180E379B63B  tmp/BalabanCMP99SourceWeightedPhysicalGaugeCovariance.draft.lean
D63D9FC2C32FEF21A9385C9698B236B7DEE97FBB2BFA3D148D158ACB2F309A93  tmp/BalabanCMP99SourceWeightedPhysicalGaugeCovarianceAudit.draft.lean
A43B35C3A1F222E678640BFE4F4DC7211F8D992F3A84A62F8B9D5BC7234AD26E  tmp/BalabanCMP99SourceGaugeTransportedRetainedPair.draft.lean
3E5B2089B22BAA34C11E3AAE1C3ADAC07628C99B4485226F84C08503E5FCE4CD  tmp/BalabanCMP99SourceGaugeTransportedRetainedPairAudit.draft.lean
1AD57F1D43DB6184A547D6284C4E7134BBF90B761563424BEC3D5A51E2BB9E6B  tmp/BalabanCMP99SourceGaugeTransportedPrecisionGreen.draft.lean
9E966B9F8E4A4FA76239904B64EE92255BCDE38A259A3A65E7073D37D49BAA64  tmp/BalabanCMP99SourceGaugeTransportedPrecisionGreenAudit.draft.lean
E6CC518B06629E4CE914704E17C992A8DB4D8B3410B3ED0881E58B8098C1215C  tmp/BalabanCMP99GaugeActionBoundTransport.draft.lean
E2A0406BD7FCF93F21F74B59E206E60FBE07D9C4EC25D18C59526C42A2081755  tmp/BalabanCMP99GaugeActionBoundTransportAudit.draft.lean
```

The combined lightweight gate currently reports:

```text
LEAN_OVERLAY_TEXT_OK files=16
C6c.8a  17/17 static readouts
C6c.8b  12/12 static readouts
C6c.8c1--c4 adapters  5/5 static readouts
C6c.8c3--c4 pair  3/3 static readouts
C6c.8c5  2/2 static readouts
C6c.8c6--c7 retained pair  4/4 static readouts
C6c.8d coefficient-polymorphic precision/Green transport  8/8 static readouts
C6c.8e localized-action norm/support transport  6/6 static readouts
```

These are text/mechanism checks only and are not Lean evidence.

## Promotion mapping

Each `tmp/*.draft.lean` is copied byte-for-byte to the corresponding
`YangMills/RG/*.lean` path after removing only `.draft` from its filename.
The PRE-VALIDATION markers remain until a cold seal.  No root import, map
counter, ledger status or terminal producer changes in the diagnostic commit.

## Stop-on-first-error focal order

```text
BalabanCMP99RegionalGaugeIsometry
BalabanCMP99RegionalGaugeIsometryAudit
BalabanCMP99CovariantD0GaugeIntertwiner
BalabanCMP99CovariantD0GaugeIntertwinerAudit
BalabanCMP99SourceGaugeDeviationTransport
BalabanCMP99SourceGaugeDeviationTransportAudit
BalabanCMP99SourceWeightedPhysicalGaugeCovariance
BalabanCMP99SourceWeightedPhysicalGaugeCovarianceAudit
BalabanCMP99SourceGaugeRegularScalePair
BalabanCMP99SourceGaugeRegularScalePairAudit
BalabanCMP99SourceGaugeTransportedRetainedPair
BalabanCMP99SourceGaugeTransportedRetainedPairAudit
BalabanCMP99SourceGaugeTransportedPrecisionGreen
BalabanCMP99SourceGaugeTransportedPrecisionGreenAudit
BalabanCMP99GaugeActionBoundTransport
BalabanCMP99GaugeActionBoundTransportAudit
```

Diagnostics may use a warm Colab checkout.  A seal must use the sanctioned
cold checkout and cite the exact source SHA, toolchain, Mathlib pin, per-target
exit codes and axiom lines.  No GitHub Actions run is dispatched for
exploration.

## Semantic acceptance

- no original-side `fineSmall` argument;
- no caller-supplied original deviation bound at the source pair endpoint;
- no transport, background-covariance or `Qprime` equality as input;
- both Ubar calls are the direct-budget constructor actually used by
  `CMP99PhysicalRegionalScaleData.nextBackground`;
- c5 uses the literal block-contained contour and source weight `M^{-d}`;
- c6--c7 performs one joint recursion and derives every prefix intertwiner;
- the transformed terminal prefix is identified with the existing generated
  `weightedQprimeTower`, rather than merely being isomorphic to it;
- regular-side coercivity and Green covariance are derived through the exact,
  coefficient-polymorphic precision intertwiner and inverse uniqueness;
- this prefix deliberately does **not** rewrite either endpoint to
  `cmp99SourceGeneratedPhysicalPrecision/Green`: those use
  `cmp99SourceGeneratedPhysicalMass`, whereas the source-faithful C6c.2 chain
  uses the exact CMP85 prefix coefficient `a_j`;
- no original-side `fineSmall` is introduced at any recursive depth;
- counters remain `20/41`, `TermSource = 0`, window 15 unattained.

## Measured retraction from the earlier manifest

`BalabanCMP99SourceGaugeRegularGeneratedGreen.draft.lean` and its audit remain
preserved as valid auxiliary algebra for the older Poincare-normalized Green,
but they are no longer promotion inputs and may not be cited as the final
C6c.8d endpoint.  The missing final specialization must be written only after
C6c.2 exposes its source-faithful prefix precision/Green.  It must instantiate
the exact CMP85 coefficient, derive coercivity from C6c.2, identify inverses
by their inverse equations, and transport the same C6c.7 actions; no equality
between the two Green families may be supplied by the caller.
