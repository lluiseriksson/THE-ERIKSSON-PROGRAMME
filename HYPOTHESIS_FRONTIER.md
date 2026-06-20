# Hypothesis Frontier — THE ERIKSSON PROGRAMME

**Current as of 2026-06-14.**  This document states the honest assumption
frontier of the **verified core** (`YangMillsCore`).  Read the current
section first; the legacy section at the bottom is **archived, pre-cleanup
material that describes the EXCLUDED vacuous chain and is NOT the current
state** — it is kept only as a historical record of over-claiming and how
it was corrected.

---

## The verified core has ZERO axioms and ZERO `sorry`

`#print axioms` on **every** headline result of `YangMillsCore` returns
exactly:

```
[propext, Classical.choice, Quot.sound]
```

— Lean's three standard axioms, nothing else.  No project-specific axiom
(in particular **not** the legacy `yangMills_continuum_mass_gap`) is in
the import closure of `YangMillsCore`.  Gaps are carried as explicit
**theorem hypotheses**, never as axioms.

## The honest frontier of the M3 (lattice) mass-gap assembly

| Obligation | Status |
|---|---|
| **IR clustering bound** (`hIRbound`) | **THEOREM-FED.** Discharged by `gibbs_truncated_correlation_bound` / `sun_two_plaquette_correlator_bound` with explicit non-empty coupling windows. No carried hypothesis remains on the IR side. |
| **Strong-coupling area law** (confinement, lattice) | **THEOREM, unconditional.** Finite-volume and volume-uniform, linearized and exact-activity (`finite_volume_area_law_exp`, `normalized_exp_wilson_loop_area_law`). Carries no hypothesis. |
| **UV single-scale bound** (§6.3 Bałaban) | **CARRIED**, and now *decomposed*. The geometric-profile conditional `lattice_mass_gap_of_cluster_and_coupling` and the marginal-coupling conditional in `RG/MarginalUVMassGap.lean` are oracle-clean; coupling/summability/kernel/Gaussian scaffolding has been theorem-fed. The remaining carried input is `hRpoly`: the concrete Yang-Mills cluster-expansion-with-holes remainder activity bound for the actual gauge RG operator. It is a theorem hypothesis — never an axiom. |
| **Continuum limit / OS–Wightman reconstruction / continuum mass gap** (M4–M5, the actual Clay problem) | **OPEN MATHEMATICS.** Not carried, not axiomatized, not claimed. **Distance to the Clay prize: ~0% (<0.1%).** |

### What discharging the carried UV inputs would (and would not) buy

* Discharging `hRpoly` would make the **lattice** (M3) mass gap
  unconditional through the existing conditional assembly.  `hRpoly` is the
  Dimock/Balaban cluster expansion with holes plus the fluctuation-integral
  estimate — genuine, **months-scale** constructive QFT with no Mathlib
  primitives.  The older geometric `hg` branch remains documented as the
  irrelevant-operator mechanism; the 4D *marginal* coupling side now uses the
  theorem-fed summable profile instead (see `docs/BALABAN-SOURCE-BOUNDS.md` §4).
* Even a full M3 discharge **does not** touch M4/M5.  The Clay distance
  stays ~0% (<0.1%) until the continuum limit and reconstruction exist.

Machine-checked record: `docs/VERIFICATION-LEDGER.md` (latest addenda).
Source-grounding for the carried inputs:
[`docs/BALABAN-SOURCE-BOUNDS.md`](docs/BALABAN-SOURCE-BOUNDS.md).
Adversarial attribution/provenance audit:
[`docs/SOURCE-CLAIM-AUDIT.md`](docs/SOURCE-CLAIM-AUDIT.md).

---

<details>
<summary><b>⚠️ ARCHIVED LEGACY (pre-cleanup, v0.1–v0.30) — describes the EXCLUDED vacuous chain. NOT the current state. Historical record only.</b></summary>

> **The material below predates the 2026-05 cleanup
> (`CLEANUP_PLAN.md`, `FOUNDATIONS.md`).**  It describes the legacy
> terminal chain `L8_Terminal/ClayTheorem` and its named axiom
> `yangMills_continuum_mass_gap`, together with the vacuous target
> `clay_millennium_yangMills : ∃ m > 0` (provable by `⟨1, one_pos⟩`,
> nothing about gauge theory needed).  **All of this is EXCLUDED from
> `YangMillsCore`** — the verified core imports none of it and contains
> zero axioms.  The "frontier closed (0 remaining)" language below refers
> to that legacy *axiomatized* chain, NOT to a solved problem; it is
> exactly the kind of over-claiming the cleanup corrected.  Kept here as
> a cautionary historical record.

### Legacy terminal theorem (EXCLUDED)

```lean
-- LEGACY / EXCLUDED FROM CORE — do not cite
axiom yangMills_continuum_mass_gap :
    ∃ m_lat : LatticeMassProfile, HasContinuumMassGap m_lat
theorem clay_millennium_yangMills : ∃ m_phys : ℝ, 0 < m_phys := …  -- vacuous
```

### Legacy "frontier closed" table (EXCLUDED — refers to the axiomatized chain)

The legacy audit reported "0 hypotheses remaining" only because the single
real obligation (`hContinuumMassGap` = the Clay problem itself) had been
**promoted to the named axiom** `yangMills_continuum_mass_gap`.  That is
not progress; it is assuming the conclusion.  The current core does the
opposite: it carries gaps as hypotheses and proves only what is genuinely
proved.

### Legacy weak/strong terminal split (EXCLUDED)

| Identifier | Prop | Note |
|---|---|---|
| `ClayYangMillsTheorem` | `∃ m_phys : ℝ, 0 < m_phys` | **Vacuous** (provable without axioms) |
| `ClayYangMillsStrong` | `∃ m_lat, HasContinuumMassGap m_lat` | Substantive only relative to the `yangMills_continuum_mass_gap` axiom |

Both are outside `YangMillsCore` and are scheduled for staged removal
(`CLEANUP_PLAN.md`).

*Legacy sections last meaningful at v0.30.0 (2026-03/05); superseded by
the verified-core frontier above.*

</details>
