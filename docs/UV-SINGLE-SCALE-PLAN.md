# UV SINGLE-SCALE PLAN — discharging the sole carried M3 hypothesis

**Date:** 2026-06-12.  **Status:** design.  Scopes a *clean-core*
discharge of the §6.3 Balaban single-scale UV bound — the **sole
remaining carried hypothesis** of the lattice mass-gap assembly
(`HYPOTHESIS_FRONTIER.md`; everything else on the M3 IR side is
theorem-fed, and the area-law programme is complete).

## 1. The honest statement of the gap

The lattice mass gap is assembled by `lattice_mass_gap_of_exp_clustering_uniform`
(`YangMills/Paper/ClusteringToGap.lean`) from two inputs:

* the **IR** bound `∀ k, |covIR k| ≤ C₁·e^{−ε·k}` — **THEOREM-FED** by
  `gibbs_truncated_correlation_bound` (the B4 cluster-correlation
  campaign);
* the **UV** bound `hUV : ∀ t, |covUV t| ≤ C₂·e^{−c₀·t}` — **CARRIED**.

`covUV t` is the ultraviolet (short-distance / high-RG-scale) part of
the plaquette–plaquette truncated covariance at separation `t`.  The
target is to produce a concrete `covUV` and prove `hUV` core-cleanly
(no `sorry`, no project axioms), so the assembly becomes hypothesis-free
on the lattice side.

## 2. What is already done (reusable, in the core)

* **The geometric summation** `uv_geometric_summation`
  (`YangMills/Paper/UVSummation.lean`): if the per-scale RG remainders
  satisfy `|R_k| ≤ M·r^k` with `0 ≤ r < 1`, then
  `|∑_{k<n} R_k| ≤ M·(1−r)⁻¹`, and (with the scale–distance dictionary
  `a_k = a*/L^{k*−k}`) this exponentiates to
  `|∑ R_k| ≤ M₀(1−r)⁻¹·e^{−c₀·t}` — exactly the `hUV` shape.  **The
  summation mechanism is proved; only the per-scale input is open.**
* The Schur / Haar selection-rule layer (`ClayCore/Schur*`,
  `∫|tr U|² ≤ N_c`), the mean-0 / variance bounds the single-scale
  estimate consumes.
* `MassGapAssembly.mass_gap_bound` — the `IR + UV → single-rate`
  combiner.

## 2a. AUDIT FINDING (2026-06-12) — the existing scaffolding is vacuous

A research-grade audit of the `ClayCore` Balaban material
(`BalabanH1H2H3`, `SmallFieldBound`, `LargeFieldBound`,
`MultiscaleDecoupling`, `OscillationBound`, `CouplingControl`)
established that it is **physically vacuous** and must NOT be wired into
the assembly:

* its hypotheses are existential upper bounds on *unconstrained*
  nonnegative reals (`∀ n, ∃ R, 0 ≤ R ∧ R ≤ …`, satisfied by `R = 0`);
* `SmallFieldActivityBound.activity : Nat → Real` is an arbitrary
  sequence, never tied to the Wilson action / gauge measure;
* `MultiscaleDecoupling.lean` &c. contain no `gaugeMeasureFrom`,
  `WilsonAction`, `sunHaarProb`, or integral whatsoever;
* hence `balaban_combined_bound : BalabanHyps ⟹ …` is a sound but EMPTY
  implication (its antecedent is trivially inhabited).

This is why those files are correctly excluded from `YangMillsCore`.
**Connecting them to the mass-gap assembly is forbidden** — it would
produce a green theorem that says nothing about Yang–Mills.  The real
work is to DEFINE `R_{t,k}` as an actual RG contribution to the
two-point function and PROVE its bound, which requires the source
material specified in `docs/UV-SHOPPING-LIST.md`.  **The campaign is
blocked on that source material** (mandate point 7/8); see the shopping
list for the exact papers, definitions, and estimates needed.

## 2b. SOURCE-GROUNDED UPDATE (2026-06-12) — papers received & audited

The Balaban gauge series (CMP 95/96/98/99/102/109/116/122-I/122-II),
the Dimock trilogy (φ⁴ exposition), and the Eriksson collection were
received and audited (full mapping in `docs/UV-SHOPPING-LIST.md` §7).
Two outcomes:

1. **The fixed-lattice clustering is now UNCONDITIONAL in Lean.**
   `sun_lattice_exponential_clustering` (ledger Add. 22,
   `TwoPlaquetteCorrelator.lean`): no carried hypothesis, explicit
   non-empty β-window, `|connected corr| ≤ C·e^{−(1/2)·dist}`.  The
   §6.3 input is confirmed **continuum-only** — it is not needed for
   the fixed-lattice statement.

2. **The §6.3 target = Balaban's full UV-stability theorem** for 4D
   non-Abelian gauge theory (CMP 122-II Theorem 1, the culmination of
   his ~10-paper series).  Dimock gives the cleanest method shape but
   for scalar φ⁴, not gauge.  The realistic first brick of the
   continuum campaign is the gauge-covariant **block-averaging
   operator** (Balaban CMP 98) defined against the existing
   `gaugeMeasureFrom` core — a dedicated multi-month effort, not a
   session task.  Reconstructing it from memory is declined on honesty
   grounds; with the papers now in hand it is at least *specifiable*.

## 3. The genuine hard content — Balaban Lemma 6.2 (the per-scale bound)

The open obligation reduces to **one** per-scale estimate:

> **(UV-core)**  `∀ k, |R_k| ≤ M·r^k` — the renormalized single-scale
> error contracts geometrically across RG scales.

**HONESTY CAVEAT (2026-06-12, source audit — see
`docs/BALABAN-SOURCE-BOUNDS.md` §2).**  The scalar `|R_k| ≤ M·r^k` is a
**simplified surrogate**, NOT Bałaban's literal bound.  Bałaban CMP 122-II
Theorem 1 / [III] §2 give the *polymer-localized* bounds
`|R^{(j)}(X,…)| ≤ g_j^{κ₀}·e^{−κ d_j(X)}` (2.31[III]) and
`|R'^{(k)}(X,…)| ≤ e^{−p₀(g_k)}·e^{−κ d_k(X)}` (1.100).  The `M·r^k` form
follows ONLY under an additional coupling-flow assumption
(`g_k^{κ₀} ≤ C·r^k` or `e^{−p₀(g_k)} ≤ C·r^k`).  Thus
`uv_geometric_summation` / `lattice_mass_gap_of_per_scale_uv` (U0) consume
a hypothesis that is *weaker/simpler* than the true Bałaban statement;
the faithful carried obligation is the polymer bound PLUS the
coupling-flow assumption.  This does not weaken the existing oracle-clean
theorems (they are honest implications from their stated hypotheses) but
it sharpens what "discharging §6.3" actually requires.

**Bridge CLOSED (2026-06-12, ledger Add. 48).**  `RG/CouplingFlowBridge.coupling_flow_bridge`
proves the faithful transfer `(g_k ≤ C·rᵏ) ∧ (|R_k| ≤ A·g_k^{κ₀}) ⟹
|R_k| ≤ (A·C^{κ₀})·rᵏ` — oracle-clean.  So the surrogate `(UV-core)` now
follows from Bałaban's true polymer bound plus the coupling-flow decay,
both carried as explicit hypotheses; the open analytic content is exactly
those two inputs (the cluster expansion / Dimock fluctuation integral,
and the coupling RG stability), nothing hidden.

This is Balaban's single-scale stability (large-field / small-field
decomposition + the RG-step contraction).  The pre-existing
development under `YangMills/ClayCore/` (`BalabanH1H2H3`,
`MultiscaleDecoupling`, `SmallFieldBound`, `LargeFieldBound`,
`OscillationBound`, `CouplingControl`) carries this content but is
**deliberately excluded from `YangMillsCore`** (it routes through the
`ClayCore/BalabanRG/**` sprawl, which carries its own named
sub-hypotheses — P78 `RGBlockingMap`, P80/P81 large-field/Cauchy
bounds, the general-polymer inductive discharge, the P91 weak-coupling
window — see `ClayCore/CLAY_CORE_STATUS.md`).  None of that is
core-clean, so it cannot feed the core assembly as-is.

## 4. Brick ladder (clean-core, honest scope)

| Brick | Content | Est. |
|---|---|---|
| U0 | **The per-scale reduction — CLOSED** (oracle clean, ledger Addendum 19): `lattice_mass_gap_of_per_scale_uv` (`Paper/ClusteringToGap.lean`) reduces the covariance-level `hUV` to the sharp per-scale RG contraction `\|R_{t,k}\| ≤ (C₂·e^{−c₀t})·rᵏ`, via `Paper.uv_geometric_summation` collapsing the scale sum to constant `C₂(1−r)⁻¹`, then the banked assembly.  The lattice mass gap now holds given a SINGLE geometric per-scale contraction — the RG-level obligation Balaban's Lemma 6.2 supplies.  (Still to do: define `covUV`/`Rsc` concretely against the KP `clusterSum` + the scale dictionary `a_k = a*/L^{k*−k}` so `hcovUV` is itself a theorem.) | **U0 closed** |
| U1 | **Small-field per-scale bound:** on the small-field region the RG step is a contraction; `|R_k^{sf}| ≤ M_sf·r^k` from the analytic stability of the Gaussian-dominated step (reuse `SmallFieldBound` content, rebuilt clean). | campaign |
| U2 | **Large-field suppression:** the large-field region carries `e^{−c·(field)²}` suppression beating its entropy; `|R_k^{lf}| ≤ M_lf·r^k` (the P80/P81 content — the genuine analytic core, currently carried as named hypotheses even in the excluded tree). | campaign (hardest) |
| U3 | **Per-scale assembly** `|R_k| ≤ M·r^k` from U1+U2 (large/small split), then `uv_geometric_summation` ⟹ `hUV`. | 1 session |
| U4 | **Feed the assembly:** instantiate `lattice_mass_gap_of_exp_clustering_uniform` with the now-theorem `hUV` ⟹ the **unconditional lattice mass gap** (M3), no carried hypotheses. | 1 session |

## 5. Honest difficulty + scope statement

U2 (large-field suppression / the RG-step contraction) is the genuine
analytic heart and is a **months-scale** formalization — it is the
reason Balaban's proof is hard.  This plan does NOT pretend otherwise:
U0/U3/U4 are bounded glue, U1 is substantial, **U2 is the real
campaign**.  Pre-existing `ClayCore` material is a *reference*, not a
drop-in: it carries sub-hypotheses and lives outside the sound core, so
each brick must be rebuilt to the core's `#print axioms =
[propext, Classical.choice, Quot.sound]` standard.

**Even with U0–U4 closed, this discharges only the M3 *lattice* mass
gap.**  It does NOT touch M4/M5 (continuum limit, OS/Wightman
reconstruction, continuum mass gap) — open mathematics, off-limits.
Distance to the Clay prize after a full UV discharge: still **~0%
(<0.1%)** — the named reduced obstruction would change from "M3 UV
single-scale bound + M4/M5" to "M4/M5", which is the honest, and still
enormous, remaining gap.

## 6. Recommended opening (next session)

Start with **U0** — define `covUV` and the scale dictionary against the
banked KP `clusterSum`, and state `hUV` as the explicit target with the
geometric-summation reduction wired in (U3's `uv_geometric_summation`
call), leaving `(UV-core)` as the single carried sub-hypothesis.  That
produces an immediate, honest intermediate: the lattice mass gap
conditional on a *single, sharply-stated* per-scale contraction
`|R_k| ≤ M·r^k`, replacing the current covariance-level `hUV` with the
RG-level obligation Balaban's Lemma 6.2 actually supplies.
