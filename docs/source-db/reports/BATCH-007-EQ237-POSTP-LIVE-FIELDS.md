# Batch 007 — CMP116 Eq. (2.37) post-P live fields

**Date:** 2026-06-26

## Purpose

Batch 007 adds a non-primary, LLM-facing operational map for the CMP116 Eq. (2.37) route.

It does not re-scan the paper, promote statuses, or touch Lean. It prevents future agents from adding more wrappers when the real source obligations are fixed-`Z0'` extraction, final post-(2.37) summation, dictionaries and constants.

## Added catalog

```text
docs/source-db/catalogs/eq237-postp-live-fields.json
```

## Added cards

```text
proof.eq237.live-fields.v2
proof.eq237.fixed-z0prime-display.v2
proof.eq237.post-summation.final-z0prime.v2
proof.eq237.z0-z0prime-dictionary.v2
proof.eq237.constant-majorants.alpha5-c3.v2
proof.eq237.residual-exponent-budget.v2
proof.eq237.component-product-to-family.v2
guard.eq237.no-unsourced-splitting.v2
proof.eq237.commit-sequence.v2
request.eq237.clean-page19-20-excerpts.v2
```

## Main guardrail

```text
Do not split Eq. (2.37) into standalone normalized Z0 and Z0prime source theorems unless the source or a proved finite reindexing/majorization supports it.
```

## Expected next real source commit

```text
docs(sources): extract CMP116 Eq237 fixed-Z0prime and post-2.37 summation
```

## Honest scope

This batch is navigation and memory only. It does not prove Eq. (2.37), Eq. (2.29), Eq. (2.31), the activity/termwise estimate, Gaussian/root/Hessian/locality, flow, IR, continuum, or Clay obligations.
