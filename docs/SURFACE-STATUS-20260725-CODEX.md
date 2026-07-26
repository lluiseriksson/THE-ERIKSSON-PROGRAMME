# Surface theorem status — Codex audit, 2026-07-25

This is a read-only status record; it does not promote any candidate evidence.

## Independently reproduced

- `audit_surface_g2_relay_admissibility.py`: after fresh terminal production
  and replay, the direct-sign union is continuous from `beta=20` through
  `3409/32`. The remaining authoritative gap is exactly
  `[3409/32,1000/9]`; the relay remains `RELAY_LEMMA_UNPROVED`.
- `audit_surface_h_tail_cauchy_budget.py`: the required complex supremum is
  still `M_SUPREMUM UNSUPPLIED`; the required threshold is
  `0.002763129991...`.
- `audit_surface_remainder_k4_positive_current_regen.py`: 39 local units and
  89,856 cells pass production/replay byte equality, explicitly candidate-only.
- `audit_surface_remainder_k4_centered_lower_current_regen.py`: 6 local units
  and 55,296 cells pass, explicitly candidate-only.
- `audit_surface_remainder_k4_tbox_current_regen.py`: 15 local units and
  34,560 cells pass, explicitly candidate-only.
- The K4 crude-ball reach diagnostic gives `M_nuD_crude ~= 7.5e321`, so it is
  many orders of magnitude above the registered Cauchy budget and cannot close
  `(H_tail)`.
- The closure-gate tests pass (`9 passed`), but this only verifies that the
  repository refuses premature promotion.

## New bounded probe

`probe_surface_h_tail_cauchy_majorant.py` and its two tests reproduce the
registered Cauchy geometry. With `rho=7/100` and `delta_max=1/15`, the exact
geometric multiplier is `16.4540494958...`; therefore the normalized complex
circle supremum would have to satisfy `M < 0.0001680` (the pre-multiplier
`C_4` budget is `<0.0027632`). The finite-order raw bilinear majorant is
`2.5903529741e-12`, but it is unnormalised and still lacks both the omitted
coefficient tail and a joint complex denominator floor. The probe ends with
`NO_H_TAIL_PROMOTION`; it is a diagnostic, not a closure claim.

The new terminal manifests are
`surface-scaled-bulk-cwin3p2-mid24-terminal-20260725.json` (34 units,
7,711 t-rows, `[241/4,275/4]`) and
`surface-scaled-bulk-cwin3p2-post1635-terminal-20260725.json` (eleven rescue-300
units, 5,108 t-rows, `[1635/16,3409/32]`). All are direct-sign evidence only and
explicitly make no H-tail/G2/G6 promotion. The authoritative audit now sees
481 admissible units and one remaining beta gap, `[3409/32,1000/9]`.

## Independent adversarial audit — 2026-07-26

A bounded external review (Claude Fable 5 High, profile `masterythief`) was
requested without write access. Its claims were checked against the local
incident and preregistration files before any action. The review agrees that
the registered S2-direct route is the only current path carrying theorem load:
the direct-sign rows do not discharge `(H_tail)` while `RELAY_LEMMA_UNPROVED`
remains. It also confirms that K4 has only local candidate oracles; the
implemented complex-modulus majorants do not provide the required global
Cauchy bound. The recommended bounded experiment was then executed at the
exact R4 widening failure (`delta_max=1/100`, `t=[72/25,29/10]`, index 144,
grid 192, Arb 140). The centered carrier passed with a uniform denominator
floor `2.44253734397...`, and the live/rerun transcripts are byte-identical.
This is favorable conditioning evidence only: the exhaustive birth-and-t
cover, the R3 residual inequality, and the registered role audit are still
required before any K2 promotion.

The follow-up five-witness campaign (indices `0,50,100,144,156`) also passed
with byte-identical live/rerun pairs; the smallest uniform denominator floor
was `1.18866891920...`. These are still witness diagnostics, not a t-cover or
a remainder certificate.

The subsequent centered-denominator campaign covered all 158 sealed t-boxes
and replayed byte-identically (`EB34F475...CC29`), with the same worst floor
at index 0. This closes only the denominator-conditioning diagnostic on the
first open delta band; the R3 residual, companion/outer-tail charges, and
the S2-direct role audit remain open.

The first centered-to-absolute R3 assembly was then tested on the critical
cell 144 and failed terminally: although `K_D>0`, the existing translated
companion/value charge gives margin `-169.6977...` (byte-identical production
and replay). This rejects that assembly, not the theorem, and prevents any
K2 promotion from the denominator cover alone.

Keeping the jet centered and evaluating the quotient directly in
`x=delta-19/2000` was also tested on cell 144. It is terminally too wide:
`Y` encloses `+/-9.02` against a budget near `2.4e-4`, with replay-identical
margin `-9.2549...`. This rejects the direct-evaluation assembly and leaves
the denominator cover as conditioning evidence only.

A preregistered scan of physical splits `1.181`, `1.19`, and `1.199` leaves
that failure unchanged (`Y=+/-9.02`, margin `-9.2549...` at all three), with
byte-identical replay. The dominant enclosure width is therefore nominal
carrier/quadrature conditioning, not the exterior split.

A centered spatial-grid scan on the same cell reduced `Y` from `+/-9.02` at
grid 192 to `+/-2.81` at grid 768, but the raw R3 margin remained
`-3.05536...`; production and replay were byte-identical. Grid refinement
alone is therefore also insufficient for K2 closure.

The exact covariance factorization was independently prototyped. A positive
pointwise mass floor removes the local `M=0` enclosure, but the centered
between-cell term remains too wide (radius `2.11e2` at grid 24, replay
identical). Thus this covariance/Hessian implementation is rejected as an R3
carrier; only the algebraic identity survives.

## Seal state

`audit_surface_final_seal.py` remains blocked by the `DO_NOT_SUBMIT` banner,
`G2=BLOCKED`, `G6=BLOCKED`, pending relay language, and an unresolved `[SLOT]`.
The definitive theorem and paper must therefore not be advertised as complete.
# Frontier subdivision diagnostic (2026-07-26)

The preregistered high-order rescue subdivision
`[1635/16,6541/64]` (orders 40/45, Arb-220, `MIN_DT=1/200000`) exceeded the
600-second wall budget without emitting a terminal row.  It is recorded as
`INCIDENT-G2-FRONTIER-SUBDIVISION-TIMEOUT-20260726.md`; no candidate manifest
was admitted and G2/G6 remain blocked.

A separate order-20/25, Arb-180 diagnostic on the same beta box also timed
out after 420 seconds without a terminal row; see
`INCIDENT-G2-FRONTIER-MIDORDER-TIMEOUT-20260726.md`.  Lowering Taylor order
therefore did not make this frontier tractable under the registered enclosure
architecture.

## Beta-frontier edge candidate (2026-07-26)

The exact remaining beta interval `[3409/32,1000/9]` corresponds to
`delta=[9/1000,32/3409]`, contained in the first terminal finite-G5 delta
band.  The new candidate-only five-family extension covers
`lambda=beta*(pi-t)` from `3/2` through `2` in 25 adjacent cells, with
production/replay byte equality and strict positive `B0` and `H` lower
endpoints.  `validate_surface_right_edge_beta106_seam_candidate.py` confirms
the arithmetic seam with the existing lambda `0..3/2` bridge.  This is edge
coverage only: the bulk interior and sign-to-`H_tail` relay remain open, so
G2/G6 are unchanged.

The corresponding order-30/37 bulk probe timed out before a terminal row, and
the latest Fable High request (profile `masterythief`) timed out without an
accepted proof or design lemma.  Neither result was promoted.

The separately requested no-tools `claude-opus-5` factorization pass also
exceeded its 240-second wall budget without a verifiable JSON response; see
`INCIDENT-G2-OPUS5-FACTORIZATION-TIMEOUT-20260726.md`.  No model-generated
claim was accepted.

## Beta-shape transport probe (2026-07-26)

The proposed endpoint-transport lemma
`Phi(beta,t)=E'(t)/exp(beta*cos(t))` convex in beta was tested independently
at 80-digit precision.  The reproducible probe
`scripts/probe_surface_g2_beta_shape.py` finds `d^2 Phi/d beta^2 < 0` at
`beta=107` for each of `t=0.6,1.5,2.5,3.0`; see
`INCIDENT-G2-BETA-SHAPE-CANDIDATE-20260726.md`.  This closes that candidate
route as a falsification result only.  It does not alter the G2/G6 blocks or
the manuscript seal state.

The seemingly stronger two-step midpoint-TP2 route was also tested directly.
At `beta=10`, the certified determinant in
`scripts/certify_two_step_midpoint_not_tp2.py` is
`[-1.17831752166...e-18 +/- 4.79e-73]` for ordered rational multiples of
`pi`; see `INCIDENT-G2-TWO-STEP-TP2-OBSTRUCTION-20260726.md`.  This removes
the midpoint stochastic-order shortcut without changing the theorem status.

The explicit high-split driver was then tested on the first residual beta box
`[3409/32,6819/64]`.  It reached the minimum t width and failed at
`t≈3.0594051819551003`; a local probe shows that beta widths `1/512` and below
can recover a negative upper bound at that one cell, but this is not an
exhaustive cover.  See `INCIDENT-G2-HIGH-SPLIT-RESIDUAL-20260726.md`.

On the K4 lane, the centred fixed-domain integrator now has a second scoped
endpoint witness at `t=2.95` for the adjacent delta boxes `[0.048,0.049]` and
`[0.049,0.05]`.  All seven weighted totals are strictly below one and the
production/replay transcripts are byte-identical.  This does not close the
global t-union or the regular/low-z K4 patch; the manifest is
`surface-remainder-k4-endpoint-strip-t295-20260726` and K4/S1'''/S2''' remain
open.

The endpoint-strip boundary probe at `t=3.10` fails `nuD_main` on the
`[0.049,0.05]` box with fraction about `1.0987`; see
`INCIDENT-K4-ENDPOINT-T310-BUDGET-20260726.md`.  Thus the two-box endpoint
contract cannot be extended by assertion across the full t-range.

A first continuous t-union fragment `[2.9,2.91]` now passes all seven rows on
the endpoint delta strip with byte-identical replay; the corresponding
manifest is `surface-remainder-k4-tbox-290-291-20260726`.  The enclosing
`[2.9,3.0]` box fails interval dependency, so no interpolation or global K4
promotion is made.

The adjacent t-box `[2.91,2.92]` also passes under the same seven-row
contract, with a byte-identical replay and its own manifest
`surface-remainder-k4-tbox-291-292-20260726`.  It remains scoped evidence;
the global K4/S1'''/S2''' gates are unchanged.

The next t-box `[2.92,2.93]` is also a current-hash, byte-replayed witness;
its manifest is `surface-remainder-k4-tbox-292-293-20260726`.

The next t-box `[2.93,2.94]` also passes and has a validator-generated scoped
manifest `surface-remainder-k4-tbox-293_294-20260726`.

The following t-box `[2.94,2.95]` fails `nuD_main` at `1.0159703820`; see
`INCIDENT-K4-TBOX-294-295-FAIL-20260726.md`.  It is deliberately excluded
from the positive manifest union.
