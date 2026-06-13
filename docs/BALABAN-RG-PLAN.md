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
| **B2** | **Coarse/fine block maps.** The canonical block section and the block-translation arithmetic. | CMP 98 (4)–(5); CMP 109 (0.4)/(0.12) | `blockBasepoint` (lower-corner section, `blockSite_blockBasepoint`); `iterShift_apply_self` (`shiftᵏ` advances the coordinate by `k mod M` — the `x(c)=x+L·e_μ` arithmetic) + `iterShift_apply_ne`. | **CLOSED** (ledger Add. 25, core 8241) |
| **B3-linear** | **Linear averaging operator `Q`** (the Gaussian / small-field limit). | CMP 95 (1.6)–(1.8) | `fineLineSum` (line integral `A(Γ_{c,x})`), `linAvg L N' A c := L^{-d} • Σ_{x∈blockOf c.source} fineLineSum A c.dir x`, with `linAvg_add` / `linAvg_smul` (linearity). | **CLOSED** (ledger Add. 24, core 8240) |
| **B3-full (interface)** | **Bałaban's axiomatic group average `M`.** The faithful route to `Ū` (CMP 109: results hold for any `M` with these properties). | CMP 109 (0.5)–(0.10) | `structure GroupAverage G` (`M : Multiset G → G`, inv-equivariance (0.5), bi-equivariance (0.6) on **nonempty** multisets; perm-inv (0.7) automatic via `Multiset`, closure (0.9) automatic) + `left/right/conj_equiv` (**gauge-covariance seed**); **non-vacuity certified** by `meanAverage` (the abelian arithmetic mean inhabits it, realising (0.8) exactly). | **CLOSED** (ledger Add. 26–27, core 8242) |
| **B3-full (analytic)** | The linearisation (0.8) `(1/i)log M(exp iA_j) = n⁻¹ΣA_j + O(‖A‖²)` (ties `M` to `Q`=`linAvg`) and Federbush inhabitation (0.10); then the operator `Ū` via CMP 109 (0.12) / CMP 98 (15). | CMP 109 (0.8),(0.10),(0.12); CMP 98 (14)–(15) [clean transcription received] | carried `GroupAverage` obligations + `Ū` def. **NEEDS a near-identity matrix-`log` framework** (matrix `exp`/`log` near `1`) — that framework is now being built (M-log layer below). | open (analytic, blocked on M-log) |
| **M-log-1** | **Near-identity logarithm: definition + convergence.** `nearLog Y = Σ_{n≥1} (-1)^{n+1}/n·Y^n` in a complete normed `ℝ`-algebra (Mathlib has `exp` but no Banach-algebra `log`). | standard; applied in CMP 109 (0.8),(0.12) | `logCoeff`, `abs_logCoeff_le_one`, `nearLog`, `norm_logCoeff_smul_pow_le`, `summable_logCoeff_smul_pow` (‖Y‖<1), `norm_nearLog_le : ‖nearLog Y‖ ≤ (1-‖Y‖)⁻¹`, `nearLog_zero`. | **CLOSED** (ledger Add. 31, core 8245) |
| **M-log-2a** | **First-order linearisation of `nearLog`** — the `O(‖·‖²)` remainder of (0.8), directly from the series tail (no `log∘exp` needed). | CMP 109 (0.8); standard | `norm_nearLog_sub_self_le : ‖nearLog Y - Y‖ ≤ ‖Y‖²/(1-‖Y‖)`. | **CLOSED** (ledger Add. 32, core 8245) |
| **M-log-2a′** | **Sharp linear bound** `‖nearLog Y‖ ≤ ‖Y‖/(1-‖Y‖)` (vanishes at `0`, i.e. `nearLog Y = O(‖Y‖)`; supersedes the `(1-‖Y‖)⁻¹` bound near `0`). | corollary of M-log-2a | `norm_nearLog_le_linear`. | **CLOSED** (ledger Add. 33, core 8245) |
| **M-log-2c** | **Scalar correctness + scalar local inverse.** `nearLog (y:ℝ) = Real.log(1+y)` (the abstract `nearLog` IS the logarithm — non-vacuity) and `nearLog(exp x - 1) = x` for `x < log 2`. | Mathlib `hasSum_pow_div_log_of_abs_lt_one`, `Real.log_exp` | `nearLog_real`, `nearLog_exp_sub_one_real`. | **CLOSED** (ledger Add. 34, core 8245) |
| **M-log-3** | **Conjugation-equivariance of `nearLog`** (single + finite-sum exponent) — `nearLog(u·Y·u⁻¹) = u·(nearLog Y)·u⁻¹` and `Σ wᵢ•nearLog(u·Yᵢ·u⁻¹) = u·(Σ wᵢ•nearLog Yᵢ)·u⁻¹`. The algebraic core of B4-Ū; with Mathlib's `NormedSpace.exp_units_conj` the full `exp[Σ…]` field map's gauge covariance is assembled. NO `log(exp)=id`. | CMP 98 (11); CMP 109 (0.12) | `nearLog_conj`, `nearLog_sum_smul_conj`. | **CLOSED** (ledger Add. 35–36, core 8245) |
| **M-log-4** | **Second-order remainder of the operator `exp`** `‖exp Z - 1 - Z‖ ≤ ‖Z‖²/(1-‖Z‖)` (i.e. `exp Z = 1+Z+O(‖Z‖²)`). With `nearLog Y = Y+O(Y²)` gives `exp(nearLog Y) = 1+Y+O(Y²)` — the (0.8) linearisation content WITHOUT `log(exp)=id`. Carries `[NormOneClass 𝔸]` (satisfied by matrix algebras). | CMP 109 (0.8); standard | `norm_expTerm_le`, `norm_exp_sub_one_sub_self_le`. | **CLOSED** (ledger Add. 38, core 8245) |
| **M-log-2b** | **`log(exp X) = X` near `0` in the OPERATOR algebra** — composition of the `exp`/`log` series; ties `nearLog`'s linearisation to `exp` and completes (0.8). The scalar case (M-log-2c) is done; the operator case needs formal-power-series composition (Mathlib gap). | BCHD.pdf; standard | `nearLog_expSub_eq` / `expSeries`-composition. | open (the genuinely hard one) |
| **B4-prep** | **Holonomy gauge-covariance along a path.** | CMP 98 (11), CMP 109 §0 | `pathEnd`, `IsPathFrom`, `wilsonLine_gaugeAct_path : wilsonLine (gaugeAct u A) es = u(a)·wilsonLine A es·u(end)⁻¹` for a connected path from `a`. | **CLOSED** (ledger Add. 28, core 8243) |
| **B4** | **Gauge covariance of the averaged contour variable** (CMP 109 (0.11)). | CMP 98 (11); CMP 109 (0.6),(0.11) | `averagedContour_gaugeAct : Avg.M (paths.map (wilsonLine (gaugeAct u A))) = u(y)·Avg.M (paths.map (wilsonLine A))·u(x)⁻¹` for a nonempty family of contours all running `y→x` — combines B4-prep (holonomy law) with `GroupAverage.biequiv` (0.6). NO matrix `log`. | **CLOSED** (ledger Add. 30, core 8244) |
| **B4-Ū (algebra)** | **Gauge covariance of the abstract `Ū`-block** `exp[Σ wᵢ•nearLog(devᵢ)]·g` (CMP 109 (0.12) shape): conjugating base + deviations by a unit conjugates the whole block. Carries only `[NormedAlgebra ℚ 𝔸]` (satisfied by `Matrix _ ℝ/ℂ`). NO `log(exp)=id`. | CMP 109 (0.12); CMP 98 (11) | `UbarBlock_conj` (`nearLog_sum_smul_conj` ∘ `NormedSpace.exp_units_conj`). | **CLOSED** (ledger Add. 37, core 8245) |
| **B4-Ū (lattice)** | Bridge the abstract group `G` to the matrix algebra `𝔸ˣ` and instantiate `UbarBlock_conj` on the lattice `Ū`. | CMP 98 (11) | `Ubar_gaugeAct`. | open (definitional `G→𝔸` bridge) |
| **B5-linear** | **Locality of `Q`.** `linAvg A c` reads only the fine bonds `⟨shiftᵏ x, c.dir, +⟩` (`x ∈` block of `c`, `k<L`). | CMP 95 (1.8), CMP 116 | `fineLineSum_congr`, `linAvg_congr`. | **CLOSED** (ledger Add. 29, core 8243) |
| **B5-full** | **Locality of `Ū`.** `Ū U` on a coarse bond reads only fine links in the adjacent blocks. | CMP 98 §A–B | `avg_local`. | open (needs `Ū`, B3-full analytic) |
| **B6** | **Norm / small-field stability.** `log avg(e^{iA}) = (linear average of A) + O(‖A‖²)`; the per-step renormalized-error bound `|R_k| ≤ M r^k`. | CMP 98 (14); 109 (small field); 122 (large field) | the bound feeding `(UV-core)` of `UV-SINGLE-SCALE-PLAN.md`. | open (needs B3–B5) |
| **B7** | **Connection to the assembly.** B6's per-scale bound is exactly the `hRsc` hypothesis of `lattice_mass_gap_of_per_scale_uv`; instantiating it discharges §6.3 and yields the continuum-uniform gap. | Eriksson [63] §6.3; UV-plan U0/U3/U4 | feed `hRsc` ⟹ `∃ gap, …` | open (needs B6) |

## B3-full design UNBLOCKED (2026-06-12) — the axiomatic group average (CMP 109)

The CMP 98 eqs (14)–(15) OCR garble is no longer a hard blocker: **CMP
109 (1987) §0, eqs (0.5)–(0.12)** gives the construction in clean,
*axiomatic* form, and Balaban states (p.253, after (0.10)) that "the
considerations and results … do not depend on any particular averaging
operation used; they are valid universally for all averages satisfying
the above properties."  So the source-faithful, non-vacuous Lean route
for B3-full is to formalise **Balaban's axiomatic group average**, not a
single transcribed formula:

* a group average `M({U_j})` is a `G_c`-valued analytic function on
  finite sets of group elements of small diameter, with:
  permutation invariance `M(π{U_j}) = M({U_j})` (0.7); the near-identity
  **linearisation** `log M({exp A_j}) = (1/n) Σ_j A_j + O(‖A‖²)` (0.8)
  — this is exactly the tie to the linear operator `Q` (brick B3-linear,
  already built); group closure `U_j ∈ G ⟹ M ∈ G` (0.9);
* an explicit inhabitant: the **Federbush average** (0.10) — `M({U_j})`
  is the `U` near all `U_j` with `Σ_j log(U_j U⁻¹) = 0` (Federbush,
  ref. [35] of CMP 109);
* the gauge field average `Ū(c) = exp[ L^{-d} Σ_{x∈B(c₋)} log(U(c₋,x)·
  U(x,x(c))⁻¹·U(x(c),c₊)·U(-c)) ] · U(c)` (CMP 109 eq (0.12)), with
  `x(c) = x + L·e_μ` the block-translated site.

Revised B3-full plan: (i) define the `GroupAverage` interface
(axioms 0.7–0.9) — non-trivially constrained (a trivial/constant `M`
violates 0.7–0.8), so NOT vacuous; (ii) define `Ū` from it via (0.12);
(iii) Federbush inhabitation (0.10) and the analytic linearisation (0.8)
are the genuinely hard pieces, carried as interface obligations
(hypotheses, never axioms) until proved.  Strategy/framing: **Lluis
Eriksson** (ai.viXra:2602.0069, 2602.0088).

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
