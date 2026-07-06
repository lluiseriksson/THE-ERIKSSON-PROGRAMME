# Eq. (2.29) / Cammarota extraction prompts

## Source keys and routing invariant

```text
primary/source-side keys:
  - cmp116.eq229.d-stage-summability
  - cmp109.ref26.cammarota-infinite-range-cluster
  - cammarota.cmp85.polymer-mayer-source-target
operational route key (repository metadata; not a primary source):
  - crosswalk.eq229.cammarota-dstage-route
```

Keep `crosswalk.eq229.cammarota-dstage-route` attached to the packet as the
public operational route to `CMP116Eq229Summability` and
`CMP116Lemma3Eq229ScaleBoundary`. The crosswalk does not extract Cammarota
Theorem 1, does not close the `DIndex`/`DParts` dictionary, and must not turn
the single Eq. (1.4) premise field into Eq. (2.29) theorem evidence.

## Prompt A: primary theorem extraction

```text
Open Cammarota CMP85, printed pages 517-528. Locate the general polymer Mayer-series theorem referenced by Balaban CMP116 for Eq. (2.29)-type summability. Extract only compact formula statements, not long prose. Record theorem number, printed page, hypotheses, constants, compatibility relation, activity/fugacity condition, and conclusion. Do not use the Springer abstract as theorem text.
```

## Prompt B: adaptation to Balaban D-families

```text
Starting from cmp116.eq229.d-stage-summability and the extracted Cammarota theorem, define the source dictionary from Balaban's D-family to Cammarota polymers. Identify the polymer activity as alpha6*exp(-delta*kappa*d_k(Y)), the compatibility/exclusion relation, and the pinned object Y0. State the exact theorem that yields sum_D prod_Y activity(Y) <= 1.
```

## Prompt C: Lean theorem target

```lean
/-- Source-fed CMP116 Eq. (2.29) D-stage summability from Cammarota. -/
theorem cmp116Eq229Summability_of_cammarota
    -- source dictionary and threshold fields here
    : CMP116Eq229Summability ...
```

## Refusal condition

If only metadata or corrupted OCR is available, do not promote. Instead update `cammarota.cmp85.polymer-mayer-source-target` with the exact failed access attempt and required artifact.
