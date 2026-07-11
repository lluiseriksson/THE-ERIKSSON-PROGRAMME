# C2 paper changelog

## Charter (commit 426d299a, 2026-07-12)
Judges J-C2-1..5 registered before any page; C1 lessons cooked in
(day-one raw logs as .txt, day-one dual hashes, no hand-assembled
predictions, same-lane self-citations from v1).

## Certified companion (commit 719c5488)
J-C2-2 PASSED: Amos bound provably strict at all 1206 pre-registered
grid points (arb prec 256, self-contained series + certified tail,
tri-state booleans, zero UNDECIDED); measured slack floor
2.782430724e-6 at (nu, x) = (0, 300); dual-hash witness committed
same commit.

## Lean integration (commit b0aa4f70)
J-C2-1 and J-C2-3 PASSED: lake build AmosClosure exit 0, 8161 jobs,
green on the FIRST run (zero API drift in the 4.30.0-rc2 -> mother-pin
port); oracle [propext, Classical.choice, Quot.sound] on all eight
theorems; rational non-vacuity witnesses with exact Pythagorean sqrt.

## v1 (commit d18a7623)
Full draft with ZERO SLOTS from birth: all build/oracle facts were
recorded, committed logs before the first page. Readable setting,
six exact statements, proof architecture (the 1/U − U = 2a/b engine
and the phi factorization in full), certified section, non-vacuity,
site-by-site closure table, related work (all classical refs
verified online; own same-lane preprints ai.viXra 2607.0020/0017/0023
cited from v1), reproducibility with theorem-to-artifact map
including the classical-cited row.

## v1.1, v1.2 (commits 1e893456, 24234652)
Overfull cleanup rounds (oracle-log token de-tokenized).

## v2 (three-desk audit round applied)
Math referee: all six statements verified character-for-character,
all hand re-derivations confirm; D1/D2 (forward-dated release
facts) -> reworded to future tense until the tag exists; D3
(calibration generic, not through AmosBound) -> abstract, intro,
Definition scope corrected; D4 -> site table now credits both phi
theorems; D5 nits (SU(2) qualifier, changelog gaps) applied.
Hostile editor (15 findings): abstract copies/toolchains count
corrected (two Lean copies on ONE off-pin toolchain + one unchecked
numerical site); 'eight' decomposed; consumer/site/pin/off-pin
defined; mother -> central; twin-desk figure re-scoped as
reconstructed external loose lower bound; 'before the script
existed' -> witnessed commit order; journal register throughout;
build facts reworded to what the artifacts witness.
Numeric auditor: CRITICAL-none; ONE soundness finding - tail
majorant off-by-one (t_K unbucketed; enclosures non-containing by
<= 6.5e-34 rel; measured conservative at all visible points) ->
script fixed to t_K/(1-q), rerun exit 0 (identical printed values),
run 1 SUPERSEDED kept committed, new script sha 0528dadf, dual-hash
witness v2; defect + audit + fix recorded in the paper as
rem:tail.
