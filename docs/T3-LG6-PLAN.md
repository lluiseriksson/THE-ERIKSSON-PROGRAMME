# T3 / LG6 — centre invariance of the gauge measure: scoping notes

**Status:** OPEN.  Goal: the Wilson-loop centre selection rule — combine the
proved algebraic eigenvalue identity `wilsonLoop_scalarCenter_smul`
(`WilsonLine.lean`: `wilsonLoop (z·A) es = ω^L · wilsonLoop A es` for scalar
central `z = ω·1`) with invariance of `gaugeMeasureFrom μ` under the centre
action, to conclude `E[wilsonLoop] = 0` whenever `ω^L ≠ 1` (i.e. `N ∤ L`).

## The assembly equation (once invariance is in hand)

`E[W] = E[W ∘ (centre action)] = E[ω^L·W] = ω^L·E[W]` ⇒ `(1−ω^L)·E[W] = 0`
⇒ `E[W] = 0` when `ω^L ≠ 1` — same `linear_combination` pattern as
`sunHaarProb_trace_pow_complex_integral_zero` (`SchurMomentVanishing.lean`).

## The measure step — recommended route (integral identity, no instances)

`gaugeMeasureFrom μ = Measure.map gaugeConfigEquiv (Measure.pi fun _ => μ)`
(`L1_GibbsMeasure/GibbsMeasure.lean:71`).  Prove directly:

`∫ f (centreAct z A) ∂(gaugeMeasureFrom μ) = ∫ f A ∂(gaugeMeasureFrom μ)`

via: `MeasureTheory.integral_map` (measurable equiv side), then transport the
centre action through `gaugeConfigEquiv` to a **coordinatewise** map on
`PosEdge → G`, then `MeasurePreserving.pi` with
`measurePreserving_mul_left μ z` (needs `[μ.IsMulLeftInvariant]` and the
measurable-group instances on `G`), then `MeasurePreserving.integral_comp`.

## ⚠ The subtlety found during scoping (do not skip)

The naive diagonal action `(z·A) e = z * A e` **on all edges** generally
violates the gauge-configuration constraint `A(−e) = A(e)⁻¹`: for central
`z`, `(z·A)(−e) = z·A(e)⁻¹` but `((z·A) e)⁻¹ = z⁻¹·A(e)⁻¹` — these agree only
if `z = z⁻¹`.  Resolution options, to be checked against the actual
`GaugeConfig`/`FiniteLatticeGeometry` definitions (`L0_Lattice/`):
1. If `GaugeConfig` is unconstrained functions on (positive) edges, the
   issue vanishes — act coordinatewise on positive edges and define the
   action on a general edge by the sign convention; then
   `wilsonLine_center_smul`'s hypothesis `∀ e, Az e = z * A e` must be
   re-derived for the *signed* action restricted to loops traversing
   positive edges, or the loop lemma re-proved for the signed action.
2. Restrict the headline to loops whose edge lists use positive edges only
   (sufficient for rectangular Wilson loops after orientation bookkeeping).
3. For `Z_N ⊂ SU(N)` with `N = 2` the constraint is automatic (`z = z⁻¹`);
   do NOT silently specialize — that would be vacuous-adjacent for the
   general claim.

First session step: read `L0_Lattice/GaugeConfigurations.lean` and
`GaugeMarginal.lean` (`gaugeMeasureFrom_map_eval` pattern) to fix which
option is structurally true, then state the centre action accordingly.

All of this is **M3 lattice-side** (Wilson-loop form); none affects
M4/M5/Clay (`docs/DEPENDENCY-GRAPH.md` §2).
