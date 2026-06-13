# UV-U1 SMALL-FIELD PLAN — the small-field per-scale contraction

**Date:** 2026-06-12.  **Status:** OPEN (brick S1 in progress).

Refines brick **U1** of `docs/UV-SINGLE-SCALE-PLAN.md` (the small-field
half of the per-scale RG-stability bound `|R_k| ≤ M·rᵏ`), now that the
local averaging-operator theory is complete (`docs/BALABAN-RG-PLAN.md`,
21 oracle-clean bricks).

## The mechanism (why the small-field step contracts)

In the small-field region the gauge field is `U_b = exp(i a_b)` with `a`
a small Lie-algebra-valued bond field, and the renormalization-group
block-spin step acts on `a` (to leading order) by the **linear averaging
operator `Q = linAvg`** (`RG/LinearAveraging.lean`); the non-abelian
corrections are `O(‖a‖²)` and controlled by the near-identity log/exp
layer (`RG/NearLog.lean`, the quantitative (0.8)
`exp(nearLog Y)=1+Y+O(‖Y‖²)` and small-field stability
`‖exp(nearLog Y)-1‖ ≤ ‖Y‖+O(‖Y‖²)`, ledger Add. 39/41).

The contraction is **not** a sup-norm contraction (the map is the
identity to first order, and the coarse bond integrates `L` fine bonds
so it *grows* by `~L` on a constant field).  It is an **ℓ²/variance
contraction** that appears only after the RG **field rescaling** and the
**ℓ²(lattice) operator assembly with multiplicity accounting**: brick S1
supplies the certified Cauchy–Schwarz mean-square bound
`‖Q A c‖² ≤ L^{1-d}·∑_{block}‖A‖²`; the Gaussian (propagator) step (S2)
turns the rescaled version into the genuine per-scale contraction.  S1
alone is the operator input, not the contraction itself.

## Brick ladder

| Brick | Content | Status |
|---|---|---|
| **S1** | **ℓ² Cauchy–Schwarz bound for `Q`** (certified operator input): `‖linAvg A c‖² ≤ (L^d)⁻¹·L·∑_{fine bonds in block} ‖A_b‖²`. NOT a standalone contraction (the line sum grows by `L`); the per-scale contraction needs the RG rescaling + ℓ² assembly (S2). `RG/AveragingL2.norm_linAvg_sq_le`. | **CLOSED** (ledger Add. 42, core 8247) |
| **S1'** | **ℓ²(lattice) operator contraction** (genuine, deterministic): `∑_bonds ‖Q A‖² ≤ L^{2-d}·∑_bonds ‖A‖²` — summing S1 over all bonds, each fine bond hit exactly `L` times (blocks tile the lattice + shift bijection). `L^{2-d} < 1` for `d ≥ 3` (physical `d = 4`): the bare averaging operator **is an ℓ²-contraction**. `RG/AveragingL2.linAvg_l2_le` (+ `sum_blockOf`, `shift_bijective`). | **CLOSED** (ledger Add. 43, core 8247) |
| **S2** | **Gaussian/propagator covariance contraction** (the analytic core): under the renormalized Gaussian measure the averaged field's covariance contracts geometrically across scales — the rescaled version of S1' against the renormalized Gaussian — Bałaban CMP 95–96 propagator bounds. | campaign (hard) |
| **S3** | **Non-abelian small-field correction**: the `O(‖a‖²)` deviation from the linear step (built: (0.8) + small-field stability) does not spoil S2's contraction in the small-field region. | needs S2 |
| **S4** | **Assembly** `|R_k^{sf}| ≤ M_sf·rᵏ` from S1–S3; feeds U3 of the UV plan. | needs S2,S3 |

## Honest scope

S1 is deterministic and provable now (finite-sum Cauchy–Schwarz).  **S2
is the hard analytic core** — it is genuinely Bałaban's propagator
analysis (CMP 95–96), a months-scale formalization requiring the
renormalized Gaussian measure and its covariance bounds, neither of
which exists in Mathlib.  This plan does not pretend S2 is a session
task.  Direct Clay relevance after a full U1 (let alone U2) remains
~0% (<0.1%): M4/M5 (continuum limit, OS reconstruction) untouched.
