# C5 release notes — c5-v1.0

Paper: "The diagonal Amos-type family at real order: a
machine-checked quantitative crossing classification" (10 pp,
tex+pdf same commit).  Everything below states exactly what is
proved, with the tricotomy labels of the series (exact / certified /
paper-level / verified).

## What this release contains

**1. The classification, machine-checked (known mathematics).**
For the family B_{nu,c}(x) = x/(nu+c+sqrt((nu+c)^2+x^2)):
uniform upper bound for rho_nu = I_{nu+1}/I_nu (all nu >= 0, x > 0)
IFF c <= 1/2 (`amosFamily_uniform_upper_iff`), uniform lower bound
for c >= 1 (`amosFamily_lower_of_one_le`), with the explicit
rational failure witness x_0(c) = 2/(2c-1) at nu = 0.  As
mathematics this is equivalent to Ruiz-Antolin--Segura (2016),
declared expressly; the claim is ONLY the formalization — uniform in
real order, from the Gamma-power series, inside one pinned
axiom-clean development.

**2. The quantitative crossing package (candidate-new).**
For every nu >= 0 and 1/2 < c < 1 the fixed member B_{nu,c} crosses
rho_nu EXACTLY ONCE on (0, infinity)
(`amosFamily_global_crossing`), and the crossing is:
- **transversal** — D'(x_*) > 0 with the explicit slope value;
- **strictly above the threshold** x_dagger =
  2(nu+c)sqrt(c(1-c))/(2c-1) (`crossing_threshold_strict`);
- **orienting** — rho_nu < B_{nu,c} strictly before, > strictly
  after, and conversely the sign of the gap locates x relative to
  x_* (`amosFamily_crossing_orientation`);
- **localized** in the constructive window
  [sqrt(1-c), 2((nu+3/2)^2-(nu+c)^2)/(2c-1)];
- **scale-bounded two-sidedly** — 2(nu+c)sqrt(c(1-c)) <=
  (2c-1) x_* <= 2((nu+3/2)^2-(nu+c)^2) (`crossing_scale`).

**3. Degenerate contact excluded by theorem.**  No crossing is a
critical point of the gap D: at any hypothetical critical contact
(forced to x_dagger by the slope identity) the EXACT identity
(nu+c)^2 D''(x_dagger) = (2c-1)^3 B_{nu,c}(x_dagger) > 0 yields a
contradiction with the below-threshold orientation
(`crossing_no_critical_contact`).  Uniqueness and orientation are
therefore UNCONDITIONAL — no tangency caveat survives.

**4. The Turan inequality at real order (classical provenance).**
I_{nu+1}^2 > I_nu I_{nu+2} over the Gamma-series
(`besselIReal_turan`), completing the sandwich
2nu+1 < psi_nu < 2nu+2.  Classical mathematics
(Thiruvenkatachar--Nanjundiah; Baricz--Ponnusamy), machine-checked
here as supporting structure; the crossing results do not depend on
it.

**5. The certified companion (30/30).**  A pre-registered
interval-arithmetic run (python-flint/arb, prec 128) verifies the
crossing phenomenon at 30 hard-regime pairs
(nu in {0, 1/2, 1, pi, 10, 100} x c in {0.501, 0.6, 0.75, 0.9,
0.999}) independently of the C5 crossing theorems: verdicts by ball
signs of D and D' only, search interval from a fixed pre-registered
rule, four certificates per pair (certified opposite-sign box,
transversality on the hull, window inclusion, both scale-law sides).
All 30 pass at the first ladder rung; 0 UNDECIDED, 0 FAIL; an
independent mpmath pass (VERIFIED label, not certified) agrees
30/30.  The companion is not part of the proof and the proof does
not cite it.

## Verification statement

At the final mathematics commit `f1c87fef`: `lake build AmosClosure`
GREEN (8175 jobs); axiom oracle prints exactly
`[propext, Classical.choice, Quot.sound]` for all 110 registered
statements (74 inherited from c4-v1.0 + 36 new).  No `sorry`, no
project axioms, anywhere.  Toolchain `leanprover/lean4:v4.29.0-rc6`,
Mathlib pinned to `0764272048...` (lakefile + manifest agree).

## Limitations (stated, not fine print)

- I_nu is the IN-CORE Gamma-power-series definition; no
  identification with any external special-functions library object
  is claimed (none exists at the pinned Mathlib); the C4
  identification theorem ties it to the factorial series at integer
  orders.
- Real order means nu >= 0 (the rpow domain of the development);
  x > 0 throughout.
- The family, the classification as mathematics, and the qualitative
  crossing phenomenon are prior art (Ruiz-Antolin--Segura 2016).
  The candidate-new content is exactly the quantitative package:
  unique transversal crossing + strict explicit threshold +
  bilateral orientation + constructive window + two-sided scale law
  + tangency exclusion.  Priority sentence (prudent, verbatim from
  the charter): "We are not aware of a previous theorem giving this
  complete quantitative crossing classification for the diagonal
  family."
- One proof-engineering disclosure: the division-free tangency
  identity is closed by `linear_combination` with cofactor
  K = -2c^2(2nu+1) found by SymPy exact division; the cofactor is
  replayed entirely inside Lean's ring normalizer — the CAS plays no
  trusted role.

## Score state on record

Two scales, both registered, neither cited in the paper: 7.58/10
(lane evaluator, Amendment 7, firm through v1.1) and 5.90/10
(external evaluator, ABSOLUTE scale where 10 = historic magnitude,
Amendment 9, on v1.2 — with the first external reproduction of the
certified companion: 30/30 on an independent machine).  The
post-release ladder (6.30–6.60 on the absolute scale) is registered
in Amendment 9: third-party lake build, independent specialist
referee, bibliographic priority confirmation, stable release.

## Release verification

The authoritative clean-clone check (run 3, transcript committed):
`lake build AmosClosure` GREEN 8175 jobs; oracle 110/110 clean;
companion 30/30 PASS; tectonic compiles; all four canonical hashes
re-derived from committed blobs match the manifest.  Runs 1–2
failed on environment defects (registered with diagnoses in their
own commits; transcripts kept).
