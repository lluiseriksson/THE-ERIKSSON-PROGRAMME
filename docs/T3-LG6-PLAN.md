# T3 / LG6 — centre invariance of the gauge measure: scoping notes

**STATUS UPDATE (2026-06-10): the measure step is PROVED.**
`L1_GibbsMeasure/CenterInvariance.lean` (in `YangMillsCore`, oracle-clean):
`gaugeConfigMEquiv` (the configuration equivalence as a measurable equiv),
`centerAct` (the centre action through positive-edge coordinates — no
`map_reverse` proof needed by construction), `centerAct_apply_pos`
(`(z·A) e = z * A e` on positive edges), and **`integral_centerAct`**:
`∫ f (centerAct z A) ∂(gaugeMeasureFrom μ) = ∫ f A` for left-invariant `μ`.
Remaining for the headline selection rule: the primed line-scaling lemma
(hypothesis `∀ e ∈ es` instead of `∀ e`) and the assembly equation — see
the resolved design below.

**Original status:** OPEN.  Goal: the Wilson-loop centre selection rule — combine the
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

## ✅ RESOLVED (2026-06-10): the design is fixed

`GaugeConfig` is a **structure with the constraint**
`map_reverse : A (reverse e) = (A e)⁻¹` (`GaugeConfigurations.lean:45`),
so the naive diagonal action is indeed ill-defined.  The correct centre
action is the **signed action**: with an orientation `sgn : E → {±1}`
(`sgn (reverse e) = −sgn e`; the `PosEdge` selector used by
`gaugeConfigEquiv` in `GibbsMeasure.lean` provides it),

`(z·A)(e) := z^{sgn e} * A e`.

`map_reverse` holds **precisely because `z` is central**:
`(z·A)(rev e) = z^{−s}·A(e)⁻¹ = (z^{s}·A e)⁻¹`.  Under `gaugeConfigEquiv`
the signed action is coordinatewise left-multiplication by `z` on positive
coordinates ⇒ measure invariance via `MeasurePreserving.pi` +
`measurePreserving_mul_left` as planned.  Consequence for the eigenvalue:
a loop's centre charge is its **signed length** `#pos − #neg`; the proved
`wilsonLoop_scalarCenter_smul` (uniform `z·A e` on all traversed edges)
applies directly to loops traversing positively-oriented edges only, where
signed length = `L`.  State the headline selection rule for such loops
(rectangular Wilson loops can be so oriented), or re-prove the line-scaling
lemma for the signed action with `z^{#pos−#neg}` — both honest; the former
is smaller.

Execution order for the session: read `GibbsMeasure.lean`'s `PosEdge` /
`gaugeConfigEquiv` definitions → define `centerAct z` (structure field +
`map_reverse` by centrality) → `MeasurePreserving (centerAct z)` through
the equiv → integral identity → assembly equation.

## ⚠ The subtlety found during scoping (now resolved above; kept for record)

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
