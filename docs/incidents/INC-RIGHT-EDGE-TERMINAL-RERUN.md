# Incident: compact right-edge terminal rerun

**Date:** 2026-07-12  
**Scope:** G5 compact certificate only; no mathematical counterexample

The first monolithic `[3,20]` execution reached `beta=17.375` but hit its
external wall-time before printing a terminal verdict.  It was never eligible
as evidence.  Four smaller chunks were then started; `[3,10]`, `[10,15]`, and
`[15,17.5]` terminated, while the desktop-turn transition interrupted the
last chunk at `19.75`.

After the execution user changed, the replacement subchunks terminated but
printed `git_head=UNAVAILABLE` because Git rejected the repository ownership.
Those transcripts were rejected under the standing provenance rule despite
their strict interval boxes.  The authoritative rerun injects the repository
as `safe.directory` into the environment inherited by Python and must print
the actual executed head.  Only its terminal transcripts may enter the union
manifest and validator.

No interval target, Taylor order, splice, or box result was weakened during
the reruns.  Partial and unavailable-provenance files have no manifest and are
not referenced by the manuscript.
