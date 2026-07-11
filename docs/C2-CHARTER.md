# C2 CHARTER — "One Amos bound, three machine-checked consumers: Bessel-ratio calculus for lattice gauge expansions"

Registered 2026-07-12, BEFORE the page (same regime as C1: judges
before pages, tricotomy, transcripts-when-committed, split roles,
no sorry, no project axioms, oracle every headline, non-vacuity
mandatory).  C1 lessons COOKED IN from day one: raw logs are
committed artifacts (the repo's `*.log` gitignore rule is dodged by
naming transcripts `.txt` from the start); every committed witness
carries DUAL hashes (LF blob + CRLF worktree); the desk registers NO
hand-assembled numerical predictions (the C1 crossover slip); own
same-lane preprints are cited from the first draft (the v6.3 slip).

## What the paper IS (honest scope, fixed now)

The Amos-type upper bound on the modified-Bessel ratio,
  I_{nu+1}(x)/I_nu(x) < x / (nu + 1/2 + sqrt((nu+1/2)^2 + x^2)),
is carried TODAY as a named hypothesis in three separate places of
this programme: (a) the surface track's phi-lemma core
(surface-theorem/PhiMonotone.lean, hAmos - E' < 0 for beta <= 3.5
rides it), (b) lean-transfer-matrix/FHBessel/FHBesselAmos.lean
(hamos, the Feynman-Hellmann unit step), (c) the 2D string-tension
lane (ym-lattice-numerics/exact2d.py computes exactly these ratios).
Each copy was verified against a DIFFERENT toolchain state
((a),(b): Lean 4.30.0-rc2 / Mathlib cd3b69ba, standalone; the mother
core pin is 4.29.0-rc6 / 07642720).

C2 unifies: ONE Lean module `AmosClosure` in the mother core that
(E1) defines the bound once (`amosRHS`, `AmosBound`), (E2) re-proves
the calibration engine and ALL FIVE consumer theorems
(amos_calibration, amos_small, phi_unit_step,
phi_step_of_recurrences, unit_step_of_recurrence_and_amos,
logderiv_unit_step_increase) through that single definition, inside
the pinned mother core (portability gap closed), (E3) exhibits
rational non-vacuity witnesses with EXACT square roots (Pythagorean
calibration: nu+1/2 = 3/2, x = 2, sqrt((3/2)^2+2^2) = 5/2 exactly),
and (NEW, certified) a companion that encloses true integer-order
Bessel ratios and certifies the strict bound pointwise on a
pre-registered consumer-driven grid.

WHAT IS NOT CLAIMED: the Amos bound itself remains a CLASSICAL cited
theorem (Amos 1974; sharp forms Segura 2011, Ruiz-Antolin--Segura
2016); it is NOT formalized here.  Consumers stay conditional on the
classical bound; C2 discharges the FRAGMENTATION (three scattered,
differently-pinned carried copies -> one named Prop, one oracle, one
certified numerical witness on the consumed domain), not the bound.
No Part-I or Part-II theorem changes its tricotomy class by this
paper, and no continuum/YM significance is claimed.

## Pre-registered judges

- J-C2-1 BUILD+PORT: `lake build AmosClosure` green on the mother
  pin; ALL endpoint theorems and both non-vacuity instantiations
  print exactly [propext, Classical.choice, Quot.sound]; the shared
  definition is used by every consumer statement (no textual copies
  of the sqrt expression in theorem statements); the Part-I artifact
  surface-theorem/PhiMonotone.lean is NOT touched.
- J-C2-2 CERTIFIED COMPANION: python-flint arb, prec >= 120;
  integer-order I_nu(x) enclosed by truncated power series PLUS an
  explicit certified tail majorant (outward rounding, ball+boolean
  printed per enclosure); PRE-REGISTERED GRID (consumer-driven):
  nu in {0,...,20} x x in {0.25 step 0.25 ... 14.0} (the Part-I
  consumer box: b = 4*beta*c <= 14 for beta <= 3.5), PLUS wide
  columns x in {20, 50, 100, 200, 300} at nu in {0,...,5}.
  BOOLEAN JUDGE: every grid point must satisfy
  ratio < amosRHS PROVABLY in balls (strict; tri-state printing).
  The slack min is MEASURED and reported with dual diagnostic
  comparison against the twin desk's exact2d figure (2.5e-7 on
  [1,100]x[0.01,300] per recon) - explicitly NOT a registered
  prediction of this desk (C1 crossover lesson: this desk has not
  derived the sharp slack asymptotics and does not pretend to).
- J-C2-3 NON-VACUITY: concrete rational instance terms (not
  existentials) satisfying every hypothesis of BOTH consumer
  families, with exact-sqrt Amos verification (no approximation in
  the witness); all values positive where the true Bessel objects
  are positive; oracle-clean.
- J-C2-4 PAPER: tex+pdf same commit (tectonic); tricotomy labels
  with "exact" reserved to the Lean tier; title says
  "machine-checked"; readable definitions (the ratio, the bound, the
  phi-sequence, the unit step, what "consumer" means); proof
  architecture (the calibration identity 1/U - U = 2a/x as the
  single engine; the exact factorization of the phi step); related
  work verified online (Amos 1974, Segura 2011,
  Ruiz-Antolin--Segura 2016, DLMF 10.29(i)); OWN same-lane preprints
  cited from draft v1: ai.viXra:2607.0020 (the FH prose paper whose
  machine core FHBesselAmos.lean is), 2607.0017 (weighted Turan),
  2607.0023 (von Mises bridge / surface closure map), and C1's
  2607.0001/0005 where the toolkit is referenced; quantitative
  section (what the certified grid covers vs what consumers consume);
  reproducibility section with theorem-to-artifact map, command
  sequence, release facts, dual hashes.
- J-C2-5 AUDIT: five roles, split sessions (numeric third-library
  re-derivation of the companion; mathematical referee vs Lean
  source; hostile editor; formal+repro on the release tree; plus
  Codex if available); findings-and-resolutions logged as
  amendments; release tags c2-v1.0(.x); tags never move.

## Fallback (declared now)

If the port to the mother pin fails on API drift that resists three
attempts, the measured failures are committed and the paper carries
the two pins honestly (statement-identical theorems, two toolchains)
as an explicit limitation - no vendored Mathlib, no pin change, no
weakening of statements.
