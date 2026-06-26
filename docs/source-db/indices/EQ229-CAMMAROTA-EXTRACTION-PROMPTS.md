# Eq. (2.29) / Cammarota extraction prompts

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
