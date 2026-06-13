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

## 3. The genuine hard content — Balaban Lemma 6.2 (the per-scale bound)

The open obligation reduces to **one** per-scale estimate:

> **(UV-core)**  `∀ k, |R_k| ≤ M·r^k` — the renormalized single-scale
> error contracts geometrically across RG scales.

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
| U0 | **Define `covUV` concretely** as the high-scale tail of the polymer-expansion covariance (reuse the banked KP `clusterSum` machinery, restricted to short-range polymers / high RG scale).  Pin the scale–distance dictionary `a_k = a*/L^{k*−k}`. | 1 session |
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
