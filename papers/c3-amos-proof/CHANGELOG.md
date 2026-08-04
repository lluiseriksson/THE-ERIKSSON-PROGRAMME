# C3 manuscript changelog

## v1 (`3e9e8bd6` on main; the id `3984d0b3` recorded at c3-v1.0 is
its orphaned pre-rebase twin — see manifest Addendum 1)

Full paper against the external core-verdict checklist (8/8):
Riccati + nullcline displayed; complete zone derivation including
the decisive chain (2n+1+x^2) I_{n+1} < x I_n; the first-crossing
lemma in human form with the left-slope sign; the exact agreed
scope sentence (abstract + Section 5); artifact map with C2
inheritance pointer; the C2 grid as independent cross-check only
("the proof does not cite it"); classical-vs-new separation (no
novelty claimed for the bound or the Riccati approach, RS16 named;
contribution = first formalization + the psi-barrier as this
formalization's structural simplification); run history relegated
to Reproducibility.

## v1.1 (`dabef64c`)

Overfull sweep only (theorem-header Lean names into centered
blocks/body; axiom list centered; calibration name into the
equation tag).  No content change.

## v1.2 (release commit, tag `c3-v1.0`)

Audit round 1 (three desks; registry in docs/C3-CHARTER.md
Amendment 2).  All sustained findings applied:

- Referee D1: closing-step wording inverted the inference direction
  (read as circular); now states positivity of the left-hand
  factors passing to B - rho through 1 + rho*B > 0, matching the
  Lean.
- Referee D4: first-crossing minimality interval corrected to
  (1/4, c) with the 1/4 endpoint attributed to the zone theorem
  (matches `hleft`).
- Referee D5: phi-step scope sharpened to "every order >= 1 (every
  order at which that step is defined)".
- Hostile-editor 1 / referee D2 (SEVERE): RELEASE-MANIFEST.md now
  exists, committed together with this manuscript; sentence updated
  to say so.
- Hostile-editor 2 (SEVERE): "all 28 module statements" was
  literally false and three map rows lacked direct oracle
  witnesses.  Resolved by the strong route: oracle registry
  extended to 34 entries (six supporting lemmas registered), green
  rebuild run 9, extended log committed; prose now says "28
  registered statements" + the release-revision extension.
- Hostile-editor 3: release-tag sentence retensed (no tag asserted
  before it exists; post-tag sequencing of the release-tree audit
  stated).
- Hostile-editor 4: comma splice after the intro display fixed
  (semicolon).
- Hostile-editor 5: house jargon removed or glossed ("lane" ->
  series/companion development, "arc" -> development, "house rule"
  -> repository's audit protocol, charter referenced by path,
  Amendment 1 named).
- Hostile-editor 6: "provably strictly" -> "with certified strict
  interval enclosures" (tricotomy-consistent).
- Hostile-editor 7: full subtitles restored for viXra 2607.0023 and
  2607.0017 (match the archive listing and the C2 bibliography).
- Hostile-editor 8: "top-level namespace" -> "largest namespace".
- Hostile-editor 9: "consumer" glossed at first use.
- Run history sentence updated: nine transcripts (run 9 added).

Also in the release commit, outside the manuscript:
`AmosClosure/Oracle.lean` v2 extension (+6 entries),
`AmosClosure/AmosBarrier.lean` stale mid-thought comment removed
(referee cosmetic note; no proof change; run 9 GREEN, 8166 jobs).

## v1.3 (patch commit, tag `c3-v1.0.1`)

Release-tree audit round (manifest Addendum 1; charter Amendment 3):

- Codex desk (MEDIUM, sustained): the zone-to-psi conversion in
  Section 4.2 omitted the two-line step I_{n+1} <= x I_n (from
  2n+1+x^2 >= 1) feeding x I_{n+1}^2 <= x^2 I_{n+1} I_n --- present
  in the Lean as the two auxiliary steps inside `besselPsi_zone`,
  now displayed in full (the paper promises "the mathematics in
  full").
- Formal+repro desk: manifest "Manuscript v1" id was the orphaned
  pre-rebase twin `3984d0b3`; authoritative on-main id `3e9e8bd6`
  (Addendum 1; this file's v1 heading corrected).  No manuscript
  content change from this finding.

No mathematical statement changed; the Lean tree is untouched by
this patch (same 34-entry oracle, same build).
