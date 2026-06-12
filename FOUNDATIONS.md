# FOUNDATIONS — Honest goalposts and critical path

**Purpose.** This document is written for the next system (human or AI) that
picks up the project. It does one thing: it makes the goalposts honest and lays
the *minimum correct foundation* so that future effort is progress toward the
Clay problem rather than motion around a vacuous target.

It supersedes, as the strategic reference, the optimistic framing in
`README.md`, `ROADMAP.md`, and the version-stamped sections of
`docs/legacy/STATE_OF_THE_PROJECT.md`. It is consistent with — and builds directly on —
the three most honest documents already in the repo:
`docs/legacy/AI_ONBOARDING.md`, `docs/phase1-llogl-obstruction.md`, and
`PETER_WEYL_ROADMAP.md`, and with the `ClayPhysical.lean` "C73 fix".

The audit was performed 2026-05-28 by reading the source, not the headlines.

---

## 1. The one thing that matters: the target is vacuous

The public claim is "machine-checked proof chain to `ClayYangMillsTheorem`".
The definition (`YangMills/L8_Terminal/ClayTheorem.lean:24`) is:

```lean
def ClayYangMillsTheorem : Prop := ∃ m_phys : ℝ, 0 < m_phys
```

This is "a positive real number exists". It is closed by `⟨1, one_pos⟩`. The
repo even contains `clay_yangmills_unconditional` proving it with `G = Unit`,
`F = 0`, `β = 0`, **zero axioms**. Nothing about Yang–Mills, SU(N), gauge
fields, or a spectral gap is required to discharge it.

The "strong" target is no better. `ClayTheorem.lean:29`:

```lean
def ClayYangMillsStrong : Prop := ∃ m_lat : LatticeMassProfile, HasContinuumMassGap m_lat
```

with `HasContinuumMassGap m_lat := ∃ m>0, Tendsto (m_lat N / a(N)) (𝓝 m)` and a
fixed coordinate `a(N) = 1/(N+1)`. Take `m_lat := constantMassProfile m` (i.e.
`m_lat N = m · a(N)`); then `m_lat N / a(N) = m` for all `N`, so the limit is
`m > 0` by inspection. `constantMassProfile_continuumGap` proves exactly this.
`ClayYangMillsStrong` is therefore **also vacuous**: `m_lat` is an arbitrary
function `ℕ → ℝ` that never has to touch the Yang–Mills measure.

**Consequence.** Every "0 sorrys, 8191 jobs, proof chain to
`ClayYangMillsTheorem`" statement is true *and uninformative*. The compilation
is real; the theorem it terminates in is empty. A reader who equates
`ClayYangMillsTheorem` with the Clay mass gap is being misled — not by a bug,
but by the choice of definition.

---

## 2. The good foundation that already exists

A previous pass saw this and did the right thing. `ClayPhysical.lean`
introduces a **non-vacuous** target:

```lean
def IsYangMillsMassProfile μ plaquetteEnergy β F distP m_lat : Prop :=
  ∃ C ≥ 0, ∀ N p q,
    |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m_lat N * distP N p q)

def ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP : Prop :=
  ∃ m_lat, IsYangMillsMassProfile μ plaquetteEnergy β F distP m_lat
         ∧ HasContinuumMassGap m_lat
```

This is the right idea: the witness `m_lat` must actually bound the **Wilson
connected correlator** of the given measure `μ`. A constant profile no longer
closes it for free, because the bound now references the dynamics.

`ClayYangMillsPhysicalStrong` is the only target in the repo worth keeping as a
headline. Everything below treats it as the base and fixes what is still wrong
with it.

---

## 3. The two leaks still open in `ClayYangMillsPhysicalStrong`

`ClayYangMillsPhysicalStrong` is necessary but **not yet sufficient**. Two
escape hatches let it be satisfied without proving anything physical. A future
solver that closes it without sealing these will have produced another vacuous
result.

### Leak A — degenerate observable / measure

`IsYangMillsMassProfile` only asks for an *upper* bound on `|corr|`. If `F` is
constant, or `μ` is a point mass, or `β` is chosen so the connected correlator
vanishes identically, then `wilsonConnectedCorr ≡ 0` and **any** `m_lat`
satisfies the bound with `C = 0`. `PETER_WEYL_ROADMAP.md §6` already flags this:
the closed instance must use a non-degenerate `F` (a genuine Wilson loop in a
non-trivial representation class) and the actual Wilson–Gibbs measure.

**Fix (encode it in the type, do not leave it as a side remark):** require a
matching lower bound / non-triviality, e.g.

```lean
structure IsNondegenerateYM μ plaquetteEnergy β F : Prop where
  nontrivial_obs : ¬ (∀ g, F g = F default)          -- F is not a.e. constant
  correlator_alive :                                   -- the gap is real, not 0=0
    ∃ N p q, wilsonConnectedCorr μ plaquetteEnergy β F p q ≠ 0
```

and conjoin it to `ClayYangMillsPhysicalStrong`. Without `correlator_alive`,
the exponential-decay bound is a statement about the zero function.

### Leak B — the continuum limit is fixed by fiat

`HasContinuumMassGap` divides `m_lat N` by the **same** hand-chosen
`a(N) = 1/(N+1)` that the profile was built from. There is no asymptotic
freedom, no running coupling `β(a)`, no statement that the *physical*
correlation length stays finite as the lattice spacing → 0. The "continuum
limit" is a coordinate artifact: multiply by `a`, divide by `a`, recover the
constant. This is the single biggest piece of physics that is currently faked.

**Fix:** the continuum statement must tie the lattice spacing to the running of
the coupling, i.e. `a = a(β)` with `a(β) → 0` as `β → ∞` along the
asymptotic-freedom trajectory, and require that the *renormalized* mass
`m_lat(β) / a(β)` converge to a strictly positive constant **along that
trajectory**, with `m_lat(β)` the gap extracted from the correlator at coupling
`β`. Until that is in place, `HasContinuumMassGap` should be renamed
`HasFormalLimitAlongFixedCoordinate` so nobody mistakes it for the real thing.

**Net:** the honest non-vacuous target is

```
ClayYangMillsPhysicalStrong
  ∧ IsNondegenerateYM            (Leak A sealed)
  ∧ continuum limit tied to β(a) (Leak B sealed)
```

Reaching even this is a major theorem. It is still **not** the full Clay
problem (see §7).

---

## 4. Assets vs liabilities (what to keep, what to stop citing)

### Genuine, reusable assets (sound, oracle-clean, mathematically real)

| Asset | Location | Why it is real |
|---|---|---|
| `∫_{Haar} |tr U|² ≤ N_c` (L2.5) | `ClayCore/Schur*` | Schur orthogonality, ~170 LOC, `[propext, choice, Quot.sound]`, no sorry |
| `∫_{Haar} tr U = 0` (F0, **already done**) | `ClayCore/SchurZeroMean.lean` | `sunHaarProb_trace_re_integral_zero`, complete, no sorry. Centre-element argument (`ω·I ∈ SU(N)`), with non-triviality witness. **Note: F0 is closed — earlier drafts of this file wrongly listed it as a to-do.** |
| `∫_{Haar} (tr U)^k = 0` for `N_c ∤ k` (Z_N selection rule) | `ClayCore/SchurMomentVanishing.lean` | **New (2026-05-28).** Generalises F0 to all trace-power moments; the centre-symmetry / N-ality rule, engine of character orthogonality. Written to mirror the proven `SchurZeroMean` patterns; **pending a `lake build` + `#print axioms` pass** before being reported as closed. |
| `memLp_gt_two_integrable_sq_mul_log_sq` | `P8_PhysicalGap/MemLpLogIntegrability.lean` | Correct L^p→L·log·L envelope; pure Mathlib; no sorry. The one safe piece of §7.4 of the obstruction doc — already done |
| `rpow_le_exp_kpParameter` (r^d → e^{−m d}) | `WilsonClusterProof.lean` | Algebraic bridge, sound |
| Fubini / partition-function interchange | `integral_boltzmann_eq_sum_activities` | Sound |
| Dependency architecture (named hypotheses, frontier ledgers) | `*_FRONTIER.md`, `docs/legacy/registry/nodes.yaml` | The honest map of the problem is itself a deliverable |

These are the **cimientos** worth building on. They are small, true, and
composable.

### Liabilities (stop presenting these as progress)

| Liability | Location | Problem |
|---|---|---|
| `sunDirichletForm := (N/8)·entSq` | `BalabanToLSI.lean:37` | Placeholder, **not** a Dirichlet form. Carries no regularity. The geometric `sunDirichletForm_concrete` exists but is **not** used in the Clay chain |
| `BakryEmeryCD := LogSobolevInequality` | `BalabanToLSI.lean` | Makes `bakry_emery_lsi` literally `id`. `sun_haar_lsi` reduces to `entSq ≤ entSq` |
| `sorry` at `BalabanToLSI.lean:808` | — | Asserts `f²∈L¹ ⇒ f²·log f²∈L¹`, which is **false** on Haar (Bertrand-series counterexample in the obstruction doc) |
| The "Σ / MemLp-gated" chain | `BalabanToLSI.lean:968+` | "Closes" the sorry by assuming `MemLp f p, p>2` for all test functions — i.e. assumes the Sobolev-embedding *output*. The doc itself calls this "threading, not closure" |
| `lsi_normalized_gibbs_from_haar` | `BalabanToLSI.lean` | The one live project axiom; routes only to the **vacuous** `ClayYangMillsTheorem` |
| ~25 "BFS-dead" axioms | `docs/legacy/AXIOM_FRONTIER.md` | Declared but unreachable from any target; rhetorical weight only. Safe to delete |

### The structural problem behind the liabilities

There are **two disconnected pipelines** in the repo:

1. **LSI / Bakry–Émery (P8_PhysicalGap)** → terminates in the *vacuous*
   `ClayYangMillsTheorem`, via tautological definitions and one false-direction
   sorry. Even if every axiom here were discharged, the result would still be
   `∃ m > 0`. By `docs/legacy/AXIOM_FRONTIER.md`'s own words, this effort is "structurally
   orthogonal to closing the Clay gap".

2. **Cluster expansion / Osterwalder–Seiler / Kotecký–Preiss
   (PETER_WEYL_ROADMAP + ConnectedCorrDecay + ClayPhysical)** → terminates in
   the *non-vacuous* `ClayYangMillsPhysicalStrong`. This is the honest path.
   Its single live obligation is the real one.

**The plan's central defect is spending effort on pipeline 1.** The foundation
fix is to commit to pipeline 2 and let pipeline 1 be clearly labelled as a
formal exercise that does not bear on Clay.

---

## 5. The single genuine open obligation

Strip everything away and the real mathematical content is one statement
(`PETER_WEYL_ROADMAP §1`):

> Prove `ConnectedCorrDecay (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F distP`
> for a genuine non-trivial Wilson observable `F`, the actual SU(N_c)
> Wilson–Gibbs measure, and small β.

i.e. an honest exponential-clustering bound

```
|⟨F_p ; F_q⟩| ≤ C · exp(−m · dist(p,q)),   m > 0,
```

for the real measure. Everything in `ClayYangMillsPhysicalStrong` (with the
§3 leaks sealed) reduces to this once `F`, `β`, `distP` are non-degenerate.
This is where 100% of the genuine difficulty lives.

---

## 6. Critical path — the foundation to build, in order

This is the ordered, honest dependency graph (matches the strategist's
`PETER_WEYL_ROADMAP`, which is correct and should be the spine of the project).
Each item is a *true* statement with the *correct* hypotheses — no wrong-axiom
shortcuts.

```
F0  ∫ tr U = 0 on SU(N), N≥2                      [ALREADY DONE — SchurZeroMean.lean]
F0+ ∫ (tr U)^k = 0 for N∤k  (Z_N selection rule)   [DONE pending compile — SchurMomentVanishing.lean]
F1  ∫ |tr U|² ≤ N  (L2.5)                          [ALREADY DONE — sound]
F2  Matrix-coefficient & character API on Haar L²  [Mathlib PR, ~500-1200 LOC]  ← REAL FRONTIER STARTS HERE
F3  Peter–Weyl for compact Lie groups              [Mathlib PR, HIGH risk, ~2500-5000 LOC]
F4  Schur orthogonality for matrix coeffs/chars    [low risk given F3]
F5  Character expansion of exp(−β Re tr U),        [project-local, HIGH risk]
      with Osterwalder–Seiler coeff bound |a_ρ(β)| ≤ (C_N β)^{|ρ|}/|ρ|!
F6  Kotecký–Preiss cluster expansion → r^{dist}    [book-level, MODERATE risk]
F7  Assemble ConnectedCorrDecay for the real μ     [low risk given F6]
F8  Seal Leak A (non-degeneracy of F, μ)           [definition work]
F9  Seal Leak B (continuum limit tied to β(a))     [the asymptotic-freedom theorem — hard]
```

**Risk-reduction warmups (strongly recommended before SU(N)):**

- **U(1) end-to-end.** Peter–Weyl for U(1) *is* Fourier series on the circle,
  already in Mathlib (`Analysis.Fourier.AddCircle`). Closing F0–F7 for U(1)
  lattice gauge theory is ~2000–4000 LOC and bypasses the F3 bottleneck
  entirely. It would be the first honestly non-vacuous closure in the project.
  (`AbelianU1Witness.lean` is a starting point.)
- **SU(2) special case.** Explicit `S³` parameterisation, character formula
  `χ_n(θ)=sin((n+1)θ)/sin θ`, modified-Bessel expansion of `exp(−β cos θ)`.
  Skips generic Peter–Weyl.

**Recommended next five sessions:** F0 → degree-2/3 moment bounds → F2 (Mathlib
PR) → pick U(1) or SU(2) → execute it to a genuine `ClayYangMillsPhysicalStrong`
(leaks sealed) for that group. That single deliverable would be worth more than
the entire current `ClayYangMillsTheorem` chain.

---

## 7. The boundary that must stay visible: this is not (yet) Clay

Even F0–F9 fully closed for SU(3) would be a **lattice** result: exponential
clustering of the lattice Wilson–Gibbs measure with a controlled continuum
limit of the mass. The actual Clay Millennium problem requires, in addition:

1. **Construction of the continuum 4D quantum Yang–Mills theory** as a measure /
   set of Wightman functions satisfying the Osterwalder–Schrader (or Wightman)
   axioms — existence of the continuum theory, not just a limit of one number.
2. **A mass gap of that constructed theory**, i.e. the spectrum of the
   continuum Hamiltonian has a gap above the vacuum.

The lattice-to-continuum reconstruction (OS reconstruction, reflection
positivity survival, rotation-invariance restoration in the limit) is the
hardest part of the problem and is represented in this repo only by definitions
that are currently coordinate artifacts (`HasContinuumMassGap`) or by axioms.

**Honest framing of the maximal realistic goal of this project:** a
machine-checked proof of *uniform exponential clustering with a positive,
continuum-stable mass for lattice Yang–Mills* — a genuine and publishable
formalization result, and a real partial step — while explicitly **not**
claiming the Clay prize, whose continuum-construction half is out of scope.

---

## 8. Summary for the next solver

- Treat `ClayYangMillsTheorem` and `ClayYangMillsStrong` as **deprecated /
  vacuous**. Do not report progress against them.
- Adopt `ClayYangMillsPhysicalStrong` **+ Leak A + Leak B sealed** as the
  target.
- Abandon the LSI/Bakry–Émery pipeline as a Clay route (keep it, clearly
  labelled, as a formal LSI exercise). Do **not** try to "discharge the last
  axiom" — it only feeds the empty target, and a sound discharge requires
  rebuilding on `sunDirichletForm_concrete` anyway.
- Build the cluster-expansion path: start at F0 (`∫ tr U = 0`), do a U(1) or
  SU(2) warmup end-to-end, reuse the real assets in §4.
- Never launder a missing theorem into an axiom by dropping its hypotheses
  (the "wrong-axiom trap", `docs/phase1-llogl-obstruction.md §5`). If a
  statement needs a Dirichlet-energy / Sobolev premise, carry the premise.
- Keep §7 visible in every public document: lattice mass gap ≠ Clay.

The most valuable thing already in this repo is not the proof chain — it is the
honest frontier documentation. This file extends it. Build on the true parts.
