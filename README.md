# The Eriksson Programme

**A Lean 4 / Mathlib formalization effort toward the Yang–Mills mass gap — with honest goalposts.**

This repository is an *open, in-progress* formalization. It contains a sound, self-contained core of Lean code, a genuine mathematical frontier, and — importantly — an explicit account of what is and is not actually proved. Read [`FOUNDATIONS.md`](FOUNDATIONS.md) and [`CLEANUP_PLAN.md`](CLEANUP_PLAN.md) before [`STATE_OF_THE_PROJECT.md`](STATE_OF_THE_PROJECT.md) or any version-stamped status: they are the current strategic reference and they correct the optimistic framing earlier versions of this README carried.

> **If you are an automated prover continuing this work, start with [`HORIZON.md`](HORIZON.md).** It is written for you: the formal dependency DAG as fill-in-the-blanks Lean signatures, the verified assets to build on, the precise external blockers (Peter–Weyl and Bessel functions are *not* in Mathlib; lattice product-measure plumbing), and a triage of what is mechanical vs. genuinely open.

### Build + verify (one command)

```
lake build YangMillsCore        # the sound, compiler-verified core
```

As of 2026-05-29 this is **green (8185 jobs)** and every new result carries the clean oracle `[propext, Classical.choice, Quot.sound]` — no `sorry`, no project axioms. Confirm with:

```
lake env lean oracle_check.lean   # prints `depends on axioms: [...]` per result
```

---

## Read this first: what "proved" means here

An earlier public theorem named `clay_millennium_yangMills` (alias `ClayYangMillsTheorem`) type-checks with a clean oracle. **That theorem is, as defined, mathematically vacuous.** Its definition is

```lean
def ClayYangMillsTheorem : Prop := ∃ m_phys : ℝ, 0 < m_phys
```

— "a positive real number exists." It is closed by `⟨1, one_pos⟩`, and the repo even discharges it with `G = Unit`, `F = 0`, `β = 0`, **zero axioms**. Nothing about SU(N), gauge fields, or a spectral gap is required. The companion `ClayYangMillsStrong` is also vacuous (a constant mass profile satisfies it by inspection).

So the honest headline is *not* "the Clay problem is formalized." It is:

> A self-contained, sound Lean 4 development of the **infrastructure** for a lattice Yang–Mills mass gap, an explicit map of the real mathematical frontier, and a set of genuinely proved, reusable lemmas about SU(N) Haar integration — leaving the non-vacuous target predicates below as the real, open work.

If you want the one-paragraph truth, that is it.

---

## The sound core: `YangMillsCore`

As of 2026-05-28 the genuinely sound, Yang–Mills-relevant content has been carved out into a single buildable root, [`YangMillsCore.lean`](YangMillsCore.lean), exposed as its own `lean_lib` target:

```
lake build YangMillsCore
```

Its entire import closure was verified (by `import`-graph analysis) to touch **none** of the LSI / Balaban-RG sprawl, none of the `~25` BFS-dead axioms, and none of the vacuous-target chain. Every declaration reachable from it is `sorry`-free, project-axiom-free, and carries oracle `[propext, Classical.choice, Quot.sound]`. The 19 modules in the core are the lattice + gauge scaffolding (`L0_Lattice`), the lattice Gibbs measure (`L1_GibbsMeasure`), SU(N) compactness + Haar state construction (`P8_PhysicalGap.SUN_*`), the sound `L^p → L·log·L` envelope lemma, and the full Schur-orthogonality programme (`ClayCore/Schur*`).

[`CLEANUP_PLAN.md`](CLEANUP_PLAN.md) is the staged execution plan that built this core and that will (Stage 3) delete the ~300-file sprawl around it. The safety rule is strict: **no deletion happens until `lake build YangMillsCore` is confirmed green.** The script `scripts/cleanup_and_push.ps1` enforces exactly that — it aborts before deleting anything if the core build fails.

---

## The real target

The non-vacuous goal already exists in the tree, in `YangMills/L8_Terminal/ClayPhysical.lean`:

```lean
def IsYangMillsMassProfile μ plaquetteEnergy β F distP m_lat : Prop :=
  ∃ C ≥ 0, ∀ N p q,
    |wilsonConnectedCorr μ plaquetteEnergy β F p q| ≤ C * exp (-m_lat N * distP N p q)

def ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP : Prop :=
  ∃ m_lat, IsYangMillsMassProfile μ plaquetteEnergy β F distP m_lat
         ∧ HasContinuumMassGap m_lat
```

Here the witness mass profile must actually bound the **Wilson connected correlator** of the given measure, so a constant profile no longer closes it for free. This is the target worth keeping. It still has two leaks that must be sealed before it is sufficient (see `FOUNDATIONS.md §3`):

- **Leak A — degenerate observable.** An upper bound on `|corr|` is satisfied trivially when the correlator is identically zero (constant `F`, point-mass `μ`, or a `β` that kills the connected part). The closed instance must use a genuine non-trivial Wilson observable and the real Wilson–Gibbs measure, with non-triviality encoded in the type (`IsNondegenerateYM`), not left as a remark.
- **Leak B — continuum limit by fiat.** `HasContinuumMassGap` currently divides the lattice mass by the same hand-chosen lattice spacing the profile was built from — a coordinate artifact, with no running coupling and no asymptotic freedom. A real continuum statement must tie the spacing to `β(a)` along the asymptotic-freedom trajectory.

The honest non-vacuous target is therefore `ClayYangMillsPhysicalStrong ∧ Leak A sealed ∧ Leak B sealed`. Reaching even this is a major theorem — and, as `FOUNDATIONS.md §7` stresses, it is still a **lattice** result, not the full Clay prize (which additionally requires constructing the continuum 4D theory and proving its spectral gap).

`ClayPhysical.lean` and `L7_Continuum/ContinuumLimit.lean` currently sit on top of the sprawl. Stage 2 of the cleanup extracts their worth-keeping definitions into a self-contained `YangMills/Target/` that imports only the core + Mathlib, before the heavy originals are deleted.

---

## What is genuinely proved (the assets worth building on)

These are sound, oracle-clean, reusable, and all reachable from `YangMillsCore`:

| Asset | Location | What it is |
|---|---|---|
| `∫_{Haar} tr U = 0` (F0) | `YangMills/ClayCore/SchurZeroMean.lean` | **Done.** Fundamental zero-mean via the centre element `ω·I ∈ SU(N)`; no `sorry` |
| `∫_{Haar} (tr U)^k = 0` for `N∤k` (Z_N selection rule) | `YangMills/ClayCore/SchurMomentVanishing.lean` | **New (2026-05-28).** Generalises F0 to all trace moments via the same centre element. **Verified**: `lake build YangMillsCore` green, oracle `[propext, Classical.choice, Quot.sound]` (2026-05-29) |
| `∫_{Haar} (tr U)^a · conj(tr U)^b = 0` for `N∤(a−b)` (full Z_N grading) | `YangMills/ClayCore/SchurMixedMomentVanishing.lean` | **New (2026-05-28).** The complete N-ality selection rule — the algebraic skeleton of the area law/confinement. **Verified**: `lake build YangMillsCore` green, oracle `[propext, Classical.choice, Quot.sound]` (2026-05-29) |
| `∫_{Haar} (∏ U_{iₛjₛ})·(∏ conj U_{kₜlₜ}) = 0` for `N∤(n−m)` (matrix-coefficient Z_N rule) | `YangMills/ClayCore/SchurEntryNAlitySelection.lean` | **New (2026-05-29).** Lifts the selection rule from characters to matrix coefficients (F2/F4 layer), Peter–Weyl-free — the leading constraint on the Weingarten integrand. **Verified**: `lake build YangMillsCore` green, oracle `[propext, Classical.choice, Quot.sound]` (2026-05-29) |
| Centre-eigenfunction vanishing principle (the reusable engine) | `YangMills/ClayCore/CenterVanishing.lean` | **New (2026-05-29).** `∫ f dHaar = 0` whenever `f(ω·I·U) = c·f(U)` with `c ≠ 1`; no integrability hypothesis. All four selection rules above are two-line corollaries. The single tool to reach for on any new centre-symmetric integrand. **Verified**: `lake build YangMillsCore` green, oracle `[propext, Classical.choice, Quot.sound]` (2026-05-29) |
| `∫_{Haar} tr(U^p) = 0` for `N∤p` (Newton power-sum rule) | `YangMills/ClayCore/SchurPowerSumVanishing.lean` | **New (2026-05-29).** The trace of the *matrix* power — the generators of the character ring and the building blocks of the F5 character expansion. Eigenvalue `ω^p` (centre element is scalar, hence central). A one-line corollary of the engine. **Verified**: `lake build YangMillsCore` green, oracle `[propext, Classical.choice, Quot.sound]` (2026-05-29) |
| Eigenfunction-vanishing principle (general) | `YangMills/ClayCore/LeftInvariantVanishing.lean` | **New (2026-05-29).** The engine for *any* left-invariant measure on *any* group: `∫ f dμ = 0` if `f(g·x) = c·f(x)`, `c ≠ 1`. Typeclasses verified against Mathlib's `integral_mul_left_eq_self`. Recovers the SU(N) engine in one line; bridges to U(1) and to the lattice product measure (open Wilson lines). **Verified**: `lake build YangMillsCore` green, oracle `[propext, Classical.choice, Quot.sound]` (2026-05-29) |
| `∫_{Haar} tr(U^p)·conj(tr(U^q)) = 0` for `N∤(p−q)` (bigraded power-sum rule) | `YangMills/ClayCore/SchurMixedPowerSumVanishing.lean` | **New (2026-05-29).** The vanishing part of the Diaconis–Shahshahani covariance of power traces — the second-moment data that organises the connected correlator in the F5–F6 character expansion. Engine corollary, eigenvalue `ω^p ω̄^q`. **Verified**: `lake build YangMillsCore` green, oracle `[propext, Classical.choice, Quot.sound]` (2026-05-29) |
| `SU(1)` is trivial; `∫ f d(sunHaarProb 1) = f 1` (boundary case) | `YangMills/ClayCore/SUOneDegenerate.lean` | **New (2026-05-29).** Certifies why every selection rule needs `N_c ≥ 2`, and exposes the repo's `AbelianU1Witness` (which models U(1) as the *trivial* group SU(1)) as degenerate. The correct U(1) is the circle `unitaryGroup (Fin 1) ≅ AddCircle`. **Verified**: `lake build YangMillsCore` green, oracle `[propext, Classical.choice, Quot.sound]` (2026-05-29) |
| `∫ fourier n dHaar = δ_{n,0}` on the circle (U(1) character orthogonality) | `YangMills/ClayCore/U1FourierOrthogonality.lean` | **New (2026-05-29). The first non-vacuous exact value in the project** — a genuine `= 1` at `n=0`, not merely `= 0`. The *correct* U(1) (`AddCircle`), via the half-index translation (eigenvalue `−1`) + additive Haar invariance — the abelian form of the engine. Realises F0–F1 for U(1) (HORIZON §5), bypassing Peter–Weyl. Also includes the full orthonormality `∫ fourier m · conj(fourier n) = δ_{m,n}` (F4 for U(1)). **Verified**: `lake build YangMillsCore` green, oracle `[propext, Classical.choice, Quot.sound]` (2026-05-29) |
| `∫_{Haar} ‖tr U‖² ≤ N_c` (L2.5) | `YangMills/ClayCore/SchurL25.lean` + `Schur*` | Schur orthogonality on SU(N), oracle `[propext, Classical.choice, Quot.sound]`, no `sorry` |
| `memLp_gt_two_integrable_sq_mul_log_sq` | `YangMills/P8_PhysicalGap/MemLpLogIntegrability.lean` | Correct `L^p → L·log·L` envelope lemma; pure Mathlib, no `sorry` |
| Lattice + gauge scaffolding | `YangMills/L0_Lattice/*`, `L1_GibbsMeasure/GibbsMeasure.lean` | Finite lattice geometry, gauge configurations, Wilson action, gauge invariance, lattice Gibbs measure |
| The frontier documentation itself | `FOUNDATIONS.md`, `CLEANUP_PLAN.md`, `AXIOM_FRONTIER.md`, `PETER_WEYL_ROADMAP.md`, `docs/phase1-llogl-obstruction.md` | An honest map of the problem — a real deliverable |

### The Z_N selection rule (the new contribution)

`SchurMomentVanishing.lean` proves that for `N ∤ k`,

```
∫_{SU(N)} (tr U)^k dHaar = 0.
```

The mechanism is left-invariance of Haar under the central element `ω·I`, where `ω = exp(2πi/N)`. Substituting `U ↦ (ω·I)·U` multiplies the integrand by `ω^k`, so the integral `J` satisfies `J = ω^k·J`; since `ω^k ≠ 1` whenever `N ∤ k` (primitivity of the N-th root of unity), `J = 0`. This is the Z_N center / N-ality selection rule, and it generalises F0 (the `k = 1` case). It reuses the already-proven `scalarCenterElement` and `trace_scalarCenter_mul` from `SchurZeroMean.lean`.

---

## What to stop citing as progress (liabilities — slated for deletion)

These live in the sprawl that `CLEANUP_PLAN.md` removes once the core is confirmed green:

| Liability | Problem |
|---|---|
| `sunDirichletForm := (N/8)·entSq` (`BalabanToLSI.lean`) | A placeholder, not a Dirichlet form; carries no regularity |
| `BakryEmeryCD := LogSobolevInequality` | Makes `bakry_emery_lsi` literally `id` |
| `sorry` asserting `f² ∈ L¹ ⇒ f²·log f² ∈ L¹` | **False** on Haar (Bertrand-series counterexample in `docs/phase1-llogl-obstruction.md`) |
| `lsi_normalized_gibbs_from_haar` | The one live project axiom; routes only to the vacuous `ClayYangMillsTheorem` |
| ~25 "BFS-dead" axioms (`AXIOM_FRONTIER.md`) | Declared but unreachable from any target; disappear with the files that hold them |

### The structural issue

There were two disconnected pipelines. The **LSI / Bakry–Émery** pipeline (`P8_PhysicalGap/BalabanToLSI` + the Balaban-RG sprawl) terminates in the *vacuous* `ClayYangMillsTheorem` through tautological definitions and one false-direction `sorry`; even fully discharged it yields only `∃ m > 0`. The **cluster-expansion / Osterwalder–Seiler / Kotecký–Preiss** pipeline (`PETER_WEYL_ROADMAP` + `ConnectedCorrDecay` + `ClayPhysical`) terminates in the *non-vacuous* target and is the honest path. The cleanup commits to the second pipeline and removes the first.

---

## The single genuine open obligation

Everything non-vacuous reduces to one statement (`PETER_WEYL_ROADMAP.md §1`):

> Prove `ConnectedCorrDecay (sunHaarProb N_c) (wilsonPlaquetteEnergy N_c) β F distP` for a genuine non-trivial Wilson observable `F`, the actual SU(N_c) Wilson–Gibbs measure, and small β —
> i.e. `|⟨F_p ; F_q⟩| ≤ C · exp(−m · dist(p,q))` with `m > 0`, for the real measure.

This is where 100% of the genuine difficulty lives.

---

## Critical path (build in this order)

```
F0  ∫ tr U = 0 on SU(N), N≥2                       [DONE — SchurZeroMean.lean]
F0+ ∫ (tr U)^k = 0 for N∤k  (Z_N selection rule)    [DONE pending compile — SchurMomentVanishing.lean]
F1  ∫ ‖tr U‖² ≤ N  (L2.5)                           [DONE — sound]
F2  Matrix-coefficient & character API on Haar L²   [Mathlib PR, ~500-1200 LOC]  ← REAL FRONTIER STARTS HERE
F3  Peter–Weyl for compact Lie groups               [Mathlib PR, HIGH risk]
F4  Schur orthogonality for matrix coeffs/chars     [low risk given F3]
F5  Character expansion of exp(−β Re tr U)          [project-local, HIGH risk]
F6  Kotecký–Preiss cluster expansion → r^{dist}     [book-level, MODERATE risk]
F7  Assemble ConnectedCorrDecay for the real μ      [low risk given F6]
F8  Seal Leak A (non-degeneracy of F, μ)            [definition work]
F9  Seal Leak B (continuum limit tied to β(a))      [asymptotic freedom — hard]
```

**Recommended warmups before attacking SU(N):**

- **U(1) end-to-end.** Peter–Weyl for U(1) is Fourier series on the circle, already in Mathlib (`Analysis.Fourier.AddCircle`). Closing F0–F7 for U(1) lattice gauge theory (~2000–4000 LOC) bypasses the F3 bottleneck and would be the first honestly non-vacuous closure in the project.
- **SU(2).** Explicit `S³` parameterization, character formula `χ_n(θ) = sin((n+1)θ)/sin θ`, Bessel expansion of `exp(−β cos θ)`. Skips generic Peter–Weyl. (`L0_Lattice/SU2Basic.lean` is a starting point and is kept for this.)

A single genuine `ClayYangMillsPhysicalStrong` (leaks sealed) for U(1) or SU(2) would be worth more than the entire current `ClayYangMillsTheorem` chain.

---

## Repository layout (after cleanup)

    YangMillsCore.lean           -- the sound, self-contained root (build this)
    YangMills/
      L0_Lattice/                -- finite lattice geometry, gauge configs, Wilson action, gauge invariance
        SU2Basic.lean            -- SU(2) warmup scaffolding (kept)
      L1_GibbsMeasure/           -- lattice Gibbs measure
      P8_PhysicalGap/
        SUN_Compact.lean         -- SU(N) topology + measurability
        SUN_StateConstruction.lean
        MemLpLogIntegrability.lean   -- sound L^p → L·log·L envelope lemma
      ClayCore/
        SchurZeroMean.lean       -- F0: ∫ tr U = 0  (done)
        SchurMomentVanishing.lean-- Z_N rule: ∫ (tr U)^k = 0, N∤k  (new)
        SchurL25.lean            -- L2.5: ∫‖tr U‖² ≤ N  (done)
        Schur*.lean              -- entry/character-orthogonality steps + physical bridge
      Target/                    -- (Stage 2) decoupled non-vacuous target defs

Key documents:

- **`FOUNDATIONS.md`** — the honest goalposts, the asset/liability ledger, the critical path. **Start here.**
- **`HORIZON.md`** — a starting point written for a stronger automated prover: the formal dependency DAG as fill-in-the-blanks Lean signatures, the new assets to mine (sharp `∫|tr U|²=1`, Weingarten calculus), and a triage of what is mechanical vs bounded vs genuinely open.
- **`CLEANUP_PLAN.md`** — the staged keep/discard plan and the build-before-delete safety protocol.
- `PETER_WEYL_ROADMAP.md` — the strategic spine of the cluster-expansion path.
- `docs/phase1-llogl-obstruction.md` — why the `L·log·L` sorry cannot be closed as stated (the "wrong-axiom trap").
- `AXIOM_FRONTIER.md` — full axiom census (which are live, which are BFS-dead).
- `AI_ONBOARDING.md` — orientation for an automated contributor.
- `STATE_OF_THE_PROJECT.md` — version-by-version history (read *after* `FOUNDATIONS.md`).

---

## Build

    lake build YangMillsCore                    # the sound core (recommended)
    lake build YangMills.ClayCore.SchurL25      # a single module

Oracle check (in a scratch `.lean` file):

    import YangMillsCore
    #print axioms YangMills.sunHaarProb_trace_re_integral_zero
    #print axioms YangMills.sunHaarProb_trace_pow_complex_integral_zero
    #print axioms YangMills.ClayCore.sunHaarProb_trace_normSq_integral_le
    -- each expected: [propext, Classical.choice, Quot.sound]

Note that an oracle-clean `#print axioms` on a declaration whose *type* is vacuous tells you only that the compilation is sound — not that anything about Yang–Mills was proved. Always check what the target predicate actually says.

---

## Working rules for contributors

- Report progress only against the **non-vacuous** target (`ClayYangMillsPhysicalStrong` + Leak A + Leak B sealed). Treat `ClayYangMillsTheorem` / `ClayYangMillsStrong` as deprecated.
- Never launder a missing theorem into an axiom by dropping its hypotheses (the "wrong-axiom trap"). If a statement needs a Dirichlet-energy / Sobolev premise, carry the premise.
- Keep the boundary visible in every public claim: **lattice mass gap ≠ Clay prize.** The continuum-construction half (OS reconstruction, reflection positivity, rotation-invariance restoration) is out of scope here.
- No `sorry` in new core declarations; oracle-check before committing.
- Nothing in future work should reintroduce a dependency on the discarded sprawl.

---

Lluis Eriksson — The Eriksson Programme.
