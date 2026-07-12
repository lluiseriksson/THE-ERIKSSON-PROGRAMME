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

## AMENDMENT 1 (2026-07-12, three-desk audit round CLOSED, pre-tag)

J-C2-5 roles 1-3 delivered (independent sessions, workflow-parallel):
- MATH REFEREE: all six statements match Core.lean character-for-
  character (AmosBound placement included); ports faithful up to
  packaging; calibration identity, phi factorization, Delta =
  2m(m+1)delta, witness arithmetic, Pythagorean point, and the DLMF
  10.29.1 ratio mapping ALL re-derived by hand and confirmed; found
  D1/D2 (forward-dated tag/manifest claims -> future-tensed until
  this release), D3 (calibration is generic, NOT through AmosBound
  -> abstract/intro/Definition scope corrected), D4 (site table now
  credits phi_unit_step too), D5 ledger nits.  Ledger notes ruled
  here: (i) the charter's own 'ALL FIVE consumer theorems' phrase
  miscounted - the correct partition is 2 engine lemmas + 4
  consumer theorems (amos_small reclassified engine-side); the
  paper's partition governs.  (ii) amosBound_iff (trivial Iff.rfl)
  is intentionally outside the oracle sweep - recorded, harmless.
- HOSTILE EDITOR: 15 findings incl. the abstract's copies/toolchain
  count (two Lean copies on ONE off-pin toolchain + one unchecked
  numerical site - NOT three copies on two toolchains), unwitnessed
  present-tense release facts, jargon (consumer/site/pin/off-pin
  now defined; mother->central), twin-figure evidence status
  (reconstructed, external, loose lower bound - re-scoped), journal
  register - ALL applied in paper v2.  Citation determination
  recorded: 2607.0001/0005 not cited because C2 nowhere references
  the C1 rooted-tree/cluster toolkit (charter conditional not
  triggered); 2607.0018 different lane, correctly omitted.
- NUMERIC AUDITOR (third method: mpmath library besseli, dps 40-120):
  amosRHS three-way identical (script=Lean=paper); 135-point sample
  + full independent 1206-point sweep all strict, slack in-ball
  135/135; transcript globals and floor recomputed to 20 digits
  (2.7824307241902420344e-6); hashes bit-exact; non-vacuity exact
  fractions PASS; ONE SOUNDNESS FINDING: run-1 tail majorant
  off-by-one (t_K unbucketed) - enclosures provably non-containing
  (<= 6.5e-34 rel) though measured CONSERVATIVE at all 495 visible
  points (computed ratio above true ratio: verdicts true, method
  unsound).  RESOLUTION: majorant corrected to t_K/(1-q), rerun
  exit 0 with identical printed values, run 1 superseded and kept,
  new script sha 0528dadf inked, defect+audit+fix recorded in the
  paper as rem:tail.  The C2 lesson for the bank: audit enclosure
  METHODS for containment, not only verdicts for truth.

## AMENDMENT 2 (2026-07-12, RELEASE REGISTRY - all judges closed)

- J-C2-4 PAPER: PASSED at v2.1 (tex+pdf same commit throughout;
  zero forward-dated facts after the referee round; tricotomy
  sweep clean per hostile editor; the two Codex paper findings -
  slack trend and order-coverage scope - fixed post-tag in
  c7b07b5f; tags untouched).
- J-C2-5 AUDIT: CLOSED with FIVE documented roles:
  (1) math referee - all statements/architecture/witnesses verified,
  5 discrepancies fixed (Amendment 1);
  (2) hostile editor - 15 findings, all applied (Amendment 1);
  (3) numeric auditor - the tail-majorant soundness catch, fixed
  and re-run (Amendment 1);
  (4) Codex - mathematics PASS in full (all six proofs re-derived
  symbolically with coefficient tables; witnesses exact; run-2
  majorant logic confirmed; 3 points to 120 digits matching), two
  paper scope findings sustained -> v2.1;
  (5) formal+repro on the release tree - PASS 8/8: oracle re-run
  byte-identical, zero sorry/axiom, single-definition routing
  confirmed, charter grid pre-registration intact, companion
  re-executed byte-identically from the blob script, all 8 manifest
  hashes re-derived, supersession = exactly the one-line sha diff,
  command premises verified (cold-clone rebuild explicitly out of
  scope, single build this arc - carried as limitation).  One
  archival deviation (run-2 commit id was a pre-rebase orphan)
  fixed by manifest addendum in c2-v1.0.1.
RELEASE CHAIN: c2-v1.0 = 8fffa16f (mathematics + expedient through
Amendment 1); c2-v1.0.1 (v2.1 paper + Amendment 2 + manifest
addendum).  The C2 arc is CLOSED at this desk; remaining steps are
the owner's (preprint circulation).  Lesson bank: audit enclosure
METHODS for containment, not only verdicts (the tail catch); a
concurrent-bot rebase can orphan a commit id between capture and
push - record ids from post-push git log, not from the commit
command's local output.

## AMENDMENT 3 (2026-07-12, external review 7.1 + next-arc registration)

External tag-level review of c2-v1.0.1: 7.1/10 (as formalization
note: 7.8 weak-accept after fixes; as analysis paper: 6.1 - the
bound itself unformalized).  Independently recomputed all 1206 grid
points at 80 digits (floor matches to 20 digits).  THREE mandatory
findings, all verified at this desk before applying and fixed in
v2.2 / c2-v1.0.2: (1) manifest carried v2 hashes inside the v2.1
tag (the C1 lesson applied only halfway - addendum now stamps
tag-scoped hashes for ALL revisions); (2) stale future tense on the
release facts; (3) bibliography lacked Hornik-Grun 2013/2024 - both
verified online and added, with the why-this-bound remark the
reviewer requested (the Amos form is the one with an EXACT
calibration identity, and HG24 proves it optimal within the
generalized family - choice by mathematics, not convenience).

NEXT-ARC REGISTRATION (the reviewer's decisive jump, >8 requires
it): C2.1 = a formal Bessel interface - define besselI (n : Nat)
(x : Real) by its power series in the central pin; prove
convergence, positivity for x > 0, and the three-term recurrence
10.29.1 from the series; restate the consumer theorems over the
TRUE besselI so the recurrence hypotheses become THEOREMS and
AmosBound (over real ratios) remains the sole named hypothesis.
Fallback declared now: if the series/recurrence formalization
resists three attempts on the pin, the measured failures are
committed and the interface is carried as the named open target -
no weakening, no axioms.  Full formalization of the Amos bound
itself stays a further arc beyond the interface.
