# Bessel–Amos / Feynman–Hellmann 2D note (v3, post-review)

**An Elementary Recurrence–Amos Proof of the Unit-Step Order-Monotonicity of
(log I_ν)′, with a Feynman–Hellmann Application to Two-Dimensional Lattice
Gauge Theory** — Lluis Eriksson, July 2026.

Contents: `bessel_amos_fh.tex` / `.pdf` (7 pp) and `verify_fh.py`
(independent numerical audit: sympy symbolic identities + mpmath dps=50 grid
checks of every inequality used; run `python verify_fh.py`).

Status and honest scope:
- The continuous order-monotonicity of I_ν′/I_ν is **known**
  (Freitas–Laugesen, arXiv:1810.07461, Lemma 10). This note proves the
  **unit-step** form 0 < ρ_ν − ρ_{ν+1} < 1/x elementarily (recurrence +
  exactly-calibrated Amos bound, no Bessel zeros), shows unit-step
  monotonicity ⟺ Amos upper bound, and derives the 2D corollary:
  every character-sector mass gap of 2D Wilson lattice gauge theory
  (U(1) and SU(2)) is strictly decreasing in β.
- This is the proved 2D instance of the programme's 4D bracket
  m′(β) ≤ 0 (THE_FH_BESSEL_THEOREM, v87). Nothing is claimed about 4D.
- Lean targets (Section 5) are the exact goals for the
  lean-transfer-matrix satellite: `amos_calibration` (~30 lines, pure real
  algebra) and the recurrence-hypothesis chain.

Review trail: v1 (novelty claim corrected in-house via literature red-team) →
7.2/10 external review (unit-step scope gap) → v2 (theorem restated to what
the proof closes) → 8.0/10 → v3 (SU(2) character-coefficient normalization
fixed: c_j = I_{2j+1}(2β)/β after dividing by d_j = 2j+1; "unstated
corollary" softened).

v4 (8.35/10 review applied): explicit statement that the elementary novelty
is the UPPER bound (positivity imported from Turán); physics citations added
for the exact character-basis diagonalization (Gross–Witten PRD 21 (1980) 446;
Montvay–Münster); formalization targets rewritten as syntactically coherent
Lean 4 signatures (`amos_calibration`, `unit_step_of_recurrence_and_amos`)
with `sorry` marking the two proof obligations; repository links added to the
numerical-audit and acknowledgements sections.

v5 (8.65/10 review applied): Lean Target 2 signature now carries (hnu : 0 <= nu) for a clean amos_calibration call; PDF text-layer encoding fixed (cmap + lmodern + glyphtounicode) so extracted text is search/copy-clean.

v6 (FINAL, submitted to viXra): the algebraic core is now MACHINE-CHECKED - FHBesselAmos.lean proves amos_calibration, unit_step_of_recurrence_and_amos and logderiv_unit_step_increase with NO sorry; axiom oracle [propext, Classical.choice, Quot.sound] for all three (lake env lean, Lean 4.30.0-rc2, Mathlib cd3b69b). hrec/hamos remain classical cited inputs (honest scope in Section 5).
