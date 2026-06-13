# BALABAN GAUGE-RG CAMPAIGN — the continuum track

**Date:** 2026-06-12.  **Status:** OPEN (brick B1 in progress).

The continuum-facing renormalization-group construction.  Goal: discharge
the §6.3 UV input of the M3 assembly (`lattice_mass_gap_of_per_scale_uv`,
ledger Add. 19) non-vacuously, by building Balaban's gauge-covariant
block-spin renormalization group against the existing
`gaugeMeasureFrom` / `FinBox` lattice core — NOT the vacuous
`ClayCore/Balaban*` scaffolding (which is correctly excluded;
UV-SHOPPING-LIST §1, §7).

**Primary source for the construction:** T. Bałaban, *Averaging
Operations for Lattice Gauge Theories*, Commun. Math. Phys. **98**
(1985) 17–51 (block geometry eqs (1)–(5); averaging operator eqs
(14)–(15); gauge-covariance eq (11)).  Supporting: Bałaban CMP 95, 96
(propagators / RG transformations), 99 (regular configs, gauge
fixing), 102 (variational problem / background fields), 109 (small-field
effective actions), 116 (cluster expansions), 122-I/II (large-field).
Method exposition: J. Dimock, *RG according to Balaban* I–III (φ⁴).
**Strategy / framing / §6.3 target:** Lluis Eriksson, *Exponential
Clustering and Mass Gap for 4D SU(N) Lattice Yang–Mills via Balaban's
Renormalization Group and Multiscale Correlator Decoupling*
(ai.viXra:2602.0088 [63]); *The Balaban–Dimock Structural Package*
(ai.viXra:2602.0069 [55]).

## Lattice-core facts used

`FinBox d N := Fin d → Fin N` (the d-torus `(ℤ/N)^d`); `ConcreteEdge d N`
= `{source : FinBox d N, dir : Fin d, sign : Bool}`; `ConcretePlaquette
d N` = `{site, dir1, dir2, dir1 < dir2}`; `GaugeConfig d N G` the gauge
field.  Blocking with block size `L` requires the fine torus side to be
`L · N'`, coarsening to side `N'`.

## The exact Lean-facing brick ladder

| # | Brick | Source | Lean target (signature shape) | Status |
|---|---|---|---|---|
| **B1** | **Block lattice geometry.** The order-1 block map and its cube fiber. | CMP 98 (1)–(3) | `blockSite`, `blockSite_eq_iff_cube` (cube char `L·yᵢ ≤ xᵢ < L·yᵢ+L`), `blockSite_surjective`, `blockOf`/`mem_blockOf`, `blockOf_card = L^d`. | **CLOSED** (ledger Add. 23, core 8239) |
| **B2** | **Coarse/fine edge & plaquette maps.** Coarse bonds/plaquettes on `FinBox d N'`; the fine bonds inside a coarse bond's block-pair; `blockEdge`/`refineEdge` relations. | CMP 98 (4)–(5) | `blockEdge : ConcreteEdge d (L*N') → ...`; `coarseEdgeBlocks : ConcreteEdge d N' → Finset (FinBox d (L*N'))` (the two blocks at its ends). | open |
| **B3** | **Gauge-covariant averaging operator.** `avg : GaugeConfig(L*N') G → GaugeConfig(N') G`, the order-1 RG field map with parallel transport along the block contours `Γ_{c,x}`. | CMP 98 (14)–(15) | `avg (U : GaugeConfig d (L*N') G) : GaugeConfig d N' G`. **BLOCKED on a clean scan of eqs (14)–(15)** — the uploaded CMP 98 OCR mangles them (see §"Missing source" below). | **blocked** |
| **B4** | **Gauge covariance.** Averaging intertwines gauge transformations. | CMP 98 (11) | `avg_gaugeTransform : avg (U.gauge u) = (avg U).gauge (u ∘ blockSite-section)`. | open (needs B3) |
| **B5** | **Locality / support.** `avg U` on a coarse bond reads only fine links in the adjacent blocks. | CMP 98 §A–B | `avg_local : (DependsOnPos (avg · coarse-bond) (fine links in block-nbhd))`. | open (needs B3) |
| **B6** | **Norm / small-field stability.** `log avg(e^{iA}) = (linear average of A) + O(‖A‖²)`; the per-step renormalized-error bound `|R_k| ≤ M r^k`. | CMP 98 (14); 109 (small field); 122 (large field) | the bound feeding `(UV-core)` of `UV-SINGLE-SCALE-PLAN.md`. | open (needs B3–B5) |
| **B7** | **Connection to the assembly.** B6's per-scale bound is exactly the `hRsc` hypothesis of `lattice_mass_gap_of_per_scale_uv`; instantiating it discharges §6.3 and yields the continuum-uniform gap. | Eriksson [63] §6.3; UV-plan U0/U3/U4 | feed `hRsc` ⟹ `∃ gap, …` | open (needs B6) |

## Missing source (precise request)

The uploaded `Averaging operations.pdf` (CMP 98) has a clean OCR for the
**geometry** (eqs (1)–(5)) and the **gauge-covariance condition** (11),
but the **explicit averaging-operator formulas (14) and (15)** are
garbled by the scan (Greek/zeta symbols, the contour `Γ_{c,x}` and the
product structure are unreadable).  To implement **B3** source-faithfully
I need a **clean copy of CMP 98 page 19–20 (equations (14) and (15))**,
or the equivalent explicit definition from CMP 96 eq (1.8) (the *linear*
averaging operation the small-field limit reduces to).  Until then, B3 is
held; B1–B2 (pure geometry) and the small-field *linear* averaging (if eq
(1.8) of CMP 96 is legible) proceed independently.

## Honest scope

This is the continuum (M4) track.  Even fully completed it does not
touch OS/Wightman reconstruction (M5) or change the Clay distance
(~0%, <0.1%) until the continuum limit + reconstruction exist.  It is a
multi-month constructive-QFT formalization; each brick is oracle-checked
and the carried analytic inputs (CMP 109/122 estimates) remain explicit
hypotheses, never axioms, until proved.
