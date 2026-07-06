# H# Appendix-F Live Fields

Purpose: make the Dimock Appendix-F H# feed and the downstream rooted H# identity directly searchable without using either one to backfill raw activity, Gaussian/root, Hessian, or support fields.

## Source Anchors

Open these first:

```powershell
python scripts\source_db.py show proof.dimock.appendixf.hsharp-feed
python scripts\source_db.py show proof.rooted-hsharp-remainder.identity.v2
python scripts\source_db.py show crosswalk.dimock.appendixf-hole-cluster-route
python scripts\source_db.py show dimockii.appendix-f.cluster-with-holes
python scripts\source_db.py show dimockii.appendix-f.second-ursell.645-646
```

The Dimock Appendix-F extraction is useful only after the CMP116/Balaban activity estimate and raw-source scale family are available. It does not prove those upstream fields.

## Live Fields

| Field | Source target | Lean target | Status |
|---|---|---|---|
| activity bound feed | CMP116/Balaban activity estimate `|H(X)| <= H0 exp(-kappa d_M)` | `YangMills.RG.balabanCMP116AppendixFHsharpOfIntegratedKsharp` input hypotheses | source_pending |
| hole-cluster H# route | Dimock Appendix F cluster-with-holes construction | `YangMills.RG.balabanCMP116AppendixFHsharpOfIntegratedKsharp` | partially_source_extracted |
| Omega connectivity | Appendix-F holes relation to repository Omega/skeleton types | `YangMills.RG.omegaHolePolymerSystem_KPCriterion_volumeUniform_skeleton_exp_of_metric_bound` | dictionary_open |
| H# exponential weight | Dimock II second Ursell bound with loss `3*kappa0+3` | `YangMills.RG.appendixFHoleExpWeight` | partially_source_extracted |
| rooted H# identity | physical raw-source scale family to scalar `Rsc` rooted series | `YangMills.RG.BalabanCMP116SourceAssumptions.rooted_hsharp_remainder_identity` | dictionary_open |

## Non-Claims

- Do not infer `raw_pointwise_decay` from the Appendix-F H# bound.
- Do not infer `rooted_hsharp_remainder_identity` from Dimock's scalar architecture alone.
- Do not use H# routing to prove Gaussian pushforward, root localization, Wilson Hessian identification, local activity construction, support, or measurability.
- Do not replace Omega-connectivity and skeleton metric dictionaries with ordinary polymer overlap.

The useful next source step is to feed the CMP116/Balaban activity bound into the Appendix-F H# route, then separately identify the rooted physical `Rsc` series.
