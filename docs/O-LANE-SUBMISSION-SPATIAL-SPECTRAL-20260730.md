# O-lane Paper 10 submission record (2026-07-30)

**State:** submitted, as reported by the owner.  The public ai.viXra
identifier had not yet appeared when this record was written; it remains
`pending` until the public catalog supplies it.

## Frozen artifact

- Title: *The Modulus: a Machine-Checked Operator Bound on the Fluctuation
  Sector of the Coupled Z_2 Slice*.
- Author: Lluis Eriksson.
- Category: Mathematics - Functional Analysis.
- Submission edition: v1.9, 8 pages.
- Paper commit: `21199f408dba86db2af2f8d2c58190b0f19b7da4`.
- Formal Lean anchor: `9704b3f3c0d576bb40c43caa5360fbd64dfa1643`.
- Strict-modulus endpoint:
  [`specGap_lt`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/9704b3f3c0d576bb40c43caa5360fbd64dfa1643/YangMills/OS/SpatialSpectral.lean#L206).
- Sharp operator-bound endpoint:
  [`norm_act_le_specGap`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/9704b3f3c0d576bb40c43caa5360fbd64dfa1643/YangMills/OS/SpatialSpectral.lean#L285).
- Relative-rate endpoint:
  [`specRatio_lt_one`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/9704b3f3c0d576bb40c43caa5360fbd64dfa1643/YangMills/OS/SpatialSpectral.lean#L334).
- Fixed-extent normalised endpoint:
  [`gibbsCorr_decay_fixed_extent`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/9704b3f3c0d576bb40c43caa5360fbd64dfa1643/YangMills/OS/SpatialSpectral.lean#L805).
- Attainment endpoint:
  [`exists_attaining_fluctuation`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/9704b3f3c0d576bb40c43caa5360fbd64dfa1643/YangMills/OS/SpatialSpectral.lean#L886).
- Greatest-element endpoint:
  [`specGap_isGreatest`](https://github.com/lluiseriksson/THE-ERIKSSON-PROGRAMME/blob/9704b3f3c0d576bb40c43caa5360fbd64dfa1643/YangMills/OS/SpatialSpectral.lean#L939).
- PDF:
  [`papers/spatial-spectral/spatial_spectral.pdf`](../papers/spatial-spectral/spatial_spectral.pdf),
  106,838 bytes.
- PDF SHA-256:
  `200cfe770180f86aa725683d20424772e009ccc980c991faa7f03f99b42287b8`.
- TeX SHA-256:
  `a0d6708aecadc07b3ea67a34349876184b553a0d83dcdce7a950fd74c0eabf64`.
- Exact submitted fields:
  [`SUBMISSION-INFO.txt`](../papers/spatial-spectral/SUBMISSION-INFO.txt).

The PDF at
`C:\Users\lluis\Desktop\YangMills\ENVIAR-AHORA\spatial_spectral.pdf` is
byte-identical to the repository artifact.  The owner also reports a fresh
shallow-clone audit of paper commit `21199f40`: the repository, local, and
raw-GitHub PDF hashes agree; all four numerical-probe blocks pass; and the
committed TeX recompiles to 8 pages with 22 anchored permalinks, none outside
the formal anchor and no unresolved references.

## Machine-checked boundary

At each fixed finite extent, `specGap` is the largest modulus among
non-Perron eigenvalues and satisfies `specGap < lambda`.  Every fluctuation
observable obeys the corresponding sharp operator bound, and a nonzero
observable attains it when the state space has at least two points.  After
normalisation, `specRatio = specGap / lambda < 1`; this gives suppression
relative to the Perron scale rather than decay of the unnormalised kernel.
The composition with the Gibbs bridge yields the normalised two-point bound
at fixed extent past an explicit threshold independent of the observable.

The rate depends on the spatial extent, and no theorem bounds it uniformly
away from one.  The measured ratios approaching one are evidence, not theorem
inputs.  Reflection positivity remains untouched.  There is no `SU(N)`,
continuum, Yang--Mills mass-gap, or Clay conclusion.

## Verification checkpoint

- `lake build YangMillsCore`: 8430 jobs, success.
- Oracle: 2672 commands and answers; 2669 distinct plus three known
  duplicates, 2646 with axiom dependencies and 23 axiom-free.
- Axiom set: exactly `{propext, Quot.sound, Classical.choice}`.
- Zero `sorryAx`, zero project axioms, zero errors.
- `SpatialSpectral`: 46 declarations, all represented in the oracle.

The public author page was rechecked on 2026-07-30 and still ended at item
`[93]`, `ai.viXra.org:2607.0078`.  No identifier is inferred from submission
order or a nearby archive number.  This record moves to the public table only
after the title appears in the catalog and its public PDF has been compared
with the frozen artifact.
