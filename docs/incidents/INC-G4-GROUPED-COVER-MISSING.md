# Incident G4: grouped scaled-left cover is missing

**Date:** 2026-07-16  
**Scope:** finite-beta scaled-left bridge, `20 <= beta <= 1000/9`  
**State:** resolved 2026-07-16

The atomic validator and the independent atomic replay both pass:

```text
912 beta intervals; 4636 strict t rows
```

The separate union validator
`validate_surface_finite_beta_scaled_left_transcripts.py` does not pass on the
current tree.  Its frozen partition has 92 grouped units, beginning with
`beta_0000_0010`, `beta_0010_0020`, `beta_0020_0030`, `beta_0030_0040`, ...,
but the corresponding grouped transcript files after `beta_0020_0030` were
initially absent.  This was a coverage/provenance failure, not a numerical
sign result.

The repair regenerated all 92 grouped transcripts from the frozen source.  The
grouped validator now passes with 912 beta intervals and 4,636 strict rows,
and the fresh independent grouped replay reproduces every row exactly.  The
incident is closed; the finite scaled-left row may carry theorem load subject
to the separate bulk, K2, K4, and G5 gates remaining open elsewhere.
