# Surface remainder K4 fixed-domain design

**Date:** 2026-07-11
**State:** `IDENTITY_IMPLEMENTED`; `L3_POINT_SMOKE_PASS`;
`CENTERED_DELTA_EXPERIMENT_QUARANTINED`; `K4_OPEN`

Let `D=[0,6/5]^2`, `delta_1=1/15`, and
`Q=[0,10 sqrt(delta_1)]^2`.  For every `0<delta<=delta_1`, the
support of the registered cutoff lies inside `Q`.  In one symmetry quadrant
the exact complement can therefore be written

```text
v_comp(delta) = 4 integral_Q [1_D-chi((s^2+a^2)/delta)] f_delta(s,a) ds da.
```

This is algebraically the true integral over `D` minus the localized core.
Unlike the scaled-coordinate representation, both `D` and `Q` are fixed.
There is consequently no moving-boundary term to estimate or accidentally
omit.  With `w_delta=1_D-chi_delta`, the exact differentiated integrand is

```text
(w f)'' = w f'' + 2 w' f' + w'' f.
```

The cutoff derivatives are exactly those pre-registered in
`SURFACE-REMAINDER-PREREG.md`.  The executable identity and its strict
subdivision rule are in `scripts/surface_remainder_complement.py`; fixed
physical jets for all four mirror carriers are in
`scripts/surface_remainder_carrier_jet.py` and are checked against independent
multiprecision differentiation.

This reformulation does not pass K4.  Promotion requires finite Arb integral
enclosures for the value, first, and second derivative on every delta box,
followed by the literal weighted S1'''/S2''' judges. A box crossing either
cutoff junction must subdivide before its terminal enclosure. A finite
terminal cover may use the implemented piecewise hull: the transition formula
is evaluated only on the clipped `q` interval and its derivatives are hulled
with the zero derivatives of the adjacent constant piece. Extending the
polynomial beyond `q in [0,1]` remains forbidden.

The manifested stress-point ladder contracts from grid 32 to grid 64. At
grid 64 the second-derivative coefficient enclosures include

```text
main:   muF [2e1 +/- 2.35], nuD [-0.8 +/- 0.0711], nuF [4e0 +/- 0.470]
mirror: MD  [1.1e1 +/- 0.855], MF [-6e0 +/- 0.669],
        MD2r [-3e0 +/- 0.326], MDFr [1e0 +/- 0.497].
```

These are point-smoke enclosures, not budget inequalities. Their role is to
show finiteness, expose the true order of the endpoint layer, and size the
delta partition. K4 remains open until the same machinery covers delta boxes
and the value/first/second completion derivatives enter the weighted judges.

The first literal delta-box trials locate a separate dependency obstruction.
At the exact endpoint, spatial grids 16 (core) and 16 (completion) restore
finiteness, so there is no true singularity.  On the terminal delta interval,
halving its width from `0.001` to `0.0005`, `0.00025`, and `0.000125` reduces
the most restrictive single-box `nuD` weighted-budget fractions from about
`1.064` to `0.0794`, `0.00779`, and `0.000898`.  Thus the exact Taylor weight
works near the terminal endpoint.

The same width `0.0005` is not a global partition: its `nuD` fraction is about
`22.1` at `delta=0.05`, `1494` at `delta=0.03`, and becomes unusable near
`delta=0.01`, contrary to the independently measured true profile.  The loss
comes from inserting the full delta box into a second-order jet and then
reading its second coefficient.  K4 production therefore needs a centred
delta representation with a rigorously enclosed next derivative, or an
analytic regular patch reaching far enough from zero.  Blindly shrinking
thousands of delta boxes is rejected as a completion strategy.

## Clean-tree quarantine of the centred-delta experiment

The finite fractions recorded below were obtained while two shared carrier
files contained experimental rationalizations.  Those files are dependencies
of the frozen G5 production and were restored byte-for-byte before that
production continued.  On the restored tree, the combined K4 regression has
16 passing tests and one failing test:

```text
test_born_centered_delta_integral_is_finite: FAIL
576 cells, 100 fallbacks; all seven totals = nan.
```

Consequently the former endpoint and `delta=0.03` fractions are historical
design diagnostics only.  They are neither reproducible current-hash evidence
nor a `CENTERED_TWO_CELL_DESIGN_PASS`.  Repair must be isolated from every
frozen G5 dependency and must first restore this regression before any new
fraction is read.

## Centred-delta successor (quarantined experiment)

The experimental next-derivative repair is implemented at carrier level in
`scripts/surface_remainder_centered_delta_carrier.py`.  It uses the existing
ordinary-derivative jet through order four and the exact centred enclosure

```text
f''(c+h) in f''(c)
              + [-rho,rho] sup |f'''(c)|
              + (rho^2/2) [-1,1] sup_box |f''''|.
```

The scaled-Bessel outer derivatives are supplied by the rigorous
integral-form recurrence backend; no derivative of an asymptotic remainder
is taken.  At a transition-piece stress point, all seven value, first-, and
second-derivative enclosures overlap the independent earlier `Jet2` backend,
and fourth derivatives stay finite on the whole positive box
`[0.049,0.05]`.  Independent 80-digit differentiation also lies inside all
seven third- and fourth-derivative enclosures at the transition stress point.
An executable negative test requires subdivision whenever a cell crosses
either cutoff junction.  A first spatial-cell assembly retains the
independently centred second derivative and charges the third/fourth tracks
with the exact half-second-derivative normalization.  These are seven green
unit tests and a design
milestone only: no spatial integral, delta partition, weighted sum,
or budget inequality has yet been promoted.  K4 remains open until an
adaptive fixed-domain integrator combines the centre and whole-box tracks on
every born delta cell and the literal seven S1''' rows pass.

The first adaptive integration smoke is now finite at its born 576-cell
partition and contracts strongly at 1,152 cells.  On the preregistered
terminal delta box `[0.049,0.05]`, the literal single-box weighted fractions
at 1,152 cells are

```text
muF 0.572813   nuD 0.742899   nuF 0.693687
MD  0.179360   MF  0.033067   MD2r 0.281721   MDFr 0.039266.
```

All seven are strictly below one.  The 576-to-1,152 refinement contracts the
raw enclosures by about one order of magnitude; 110 of the final cells use
the rigorous whole-delta fallback at a cutoff junction or outside the current
`z>=20` centred companion contract.  This is an endpoint **design pass**, not
K4 evidence: no production transcript or independent rerun exists, the other
delta boxes have not been evaluated, and the regular `delta=0` patch is still
absent.

The earlier obstruction at `delta around 0.03` is also removed by spatial
refinement without changing any analytic constant.  For
`delta in [0.0300,0.0305]`, the 1,152-cell fractions are still nonterminal
(`muF 2.881`, `nuD 4.234`, `nuF 3.747`), but the registered refinement
sequence contracts them monotonically.  At 9,216 cells all seven pass:

```text
muF 0.665851   nuD 0.922033   nuF 0.816650
MD  0.103896   MF  0.014694   MD2r 0.199206   MDFr 0.021890.
```

In that experimental tree this replaced the former whole-box `nuD` design
fraction near `1494` by a strictly subunit centred enclosure at the same
location.  Under the clean-tree quarantine it is not a live two-cell design
result, a finite delta cover, or K4 certification.

The same fixed-physical integrator is deliberately rejected near the regular
endpoint.  On `[0.0100,0.01025]`, 124 cutoff-crossing fallback cells drive
the seven fractions to `10^4--10^6` even at 1,152 cells.  This is the known
moving-cutoff dependency returning in another guise, not evidence that the
true carrier derivatives diverge.  No further blind refinement is
authorized there.  The finite K4 architecture must therefore be hybrid:
the scaled regular-coordinate series and analytic outer tail supply a
`delta=0` patch, while the centred fixed-physical jets cover only the
positive range where their born refinement contracts.

## Rejected regular-endpoint realizations

Two direct implementations of that last sentence have now been falsified at
design level.  They remain useful negative results because they distinguish a
missing analytic representation from a request for more spatial subdivision.

First, rationalizing the phase and differentiating the fixed physical cells
directly does not cure the endpoint dependency.  On
`delta in [0.01,0.01025]` the seven budget fractions stay at roughly
`10^9--10^10`; even the easier box `[0.03,0.0305]` remains nonterminal, with
fractions ranging from about `88` to `24887`.  The implementation is in
`surface_remainder_direct_physical_integrator_design.py`; it is retained as a
falsifier, not a candidate certificate.

Second, merely replacing the physical coordinates by one whole-box scaled
spatial grid also fails.  At `delta in [0.02,0.0205]`, a 32-cell scaled grid
still gives representative fractions `muF=485`, `nuD=5745`, and `nuF=997`.
A centred-delta version on the same scaled core is worse (`10^4--10^6`).
These failures are produced by
`surface_remainder_scaled_centered_integrator_design.py` and show that the
regular patch must exploit the analytic ball/series structure before interval
evaluation; a coordinate rename with an unchanged whole-box dependency is
insufficient.

No K4 claim is weakened or strengthened by these failures.  The admitted
next route is a true regular-ball expansion with coefficient-wise remainders
and an analytic exterior tail, followed by overlap with the already green
centred positive-delta cells.  If that route cannot produce a strict literal
S1''' union sum, `(H_cube)` remains open and the sharpened `M_sharp` clause
cannot appear in a terminal theorem.

The coordinate-transport identity and the exact pre-registered successor are
now fixed in
[`SURFACE-REMAINDER-K4-REGULAR-BALL-PREREG.md`](SURFACE-REMAINDER-K4-REGULAR-BALL-PREREG.md).
The seven-carrier half-power audit now passes symbolically: all full masses
have integer valuation zero, and the real-coercivity, complex-disk, and Poisson
oracle gates pass as local guards.  The remaining K4 gates are an executable
transport finite-difference oracle, positive-lane overlap, and convergence
cover; no regular-ball production computation is authorized before those
three gates exist and pass.

## Independent t=2.95 endpoint witness (2026-07-26)

The same centred fixed-domain integrator was rerun at the independent stress
point `t=2.95` on the two adjacent endpoint boxes `[0.048,0.049]` and
`[0.049,0.05]`.  Production and replay are byte-identical; all seven literal
weighted totals have strict outward upper endpoint below one.  The executable
validator and manifest are
`scripts/validate_surface_remainder_k4_endpoint_strip_t295.py` and
`run-manifests/surface-remainder-k4-endpoint-strip-t295-20260726.json`.
This is a second scoped witness only: it does not supply the missing t-union,
regular endpoint patch, low-z tail, overlap theorem, or global S1'''/S2'''
certificate, so `NO_K4_PROMOTION` remains unchanged.

A continuous t-box `[2.9,2.91]` over the same delta strip also passes all seven
rows with byte-identical production/replay.  Its manifest is
`surface-remainder-k4-tbox-290-291-20260726.json`.  The wider t-box
`[2.9,3.0]` was tested and fails by interval dependency, so this result is a
scoped t-union fragment rather than an interpolation principle.

The adjacent continuous box `[2.91,2.92]` passes under the same contract and
is recorded in `surface-remainder-k4-tbox-291-292-20260726.json`.  These boxes
are intentionally kept as separate rows; no unproved monotonicity is used to
join them.

The next box `[2.92,2.93]` also passes and is recorded in
`surface-remainder-k4-tbox-292-293-20260726.json`; its tightest row is still
strictly below one (`nuD_main` upper endpoint about `0.96012`).

The following box `[2.93,2.94]` passes as well.  Its manifest was generated by
the checked-in `make_surface_remainder_k4_tbox_manifest.py`, which refuses to
write a manifest until the production/replay validator succeeds.

The next box `[2.94,2.95]` is the first negative t-box: only `nuD_main` exceeds
the budget (`1.0159703820`), despite byte-identical production/replay.  It is
recorded in `INCIDENT-K4-TBOX-294-295-FAIL-20260726.md` and has no positive
manifest.

Splitting that failed box at width `0.005` repairs the interval dependency:
both `[2.94,2.945]` and `[2.945,2.95]` pass and have validator-generated
manifests.  This is an explicit partition result, not a claim that the
unpartitioned box passes.

The width-`0.005` chain reaches `[2.955,2.96]`; the next box `[2.96,2.965]`
fails only `nuD_main` at `1.0096577405`.  It is recorded in
`INCIDENT-K4-TBOX-2960-2965-FAIL-20260726.md`; the admissible next test is a
width-`0.0025` split.

## Clean-tree regression repair (2026-07-15)

The centred positive-delta smoke exposed a purely interval-arithmetic failure:
cells whose fixed-domain complement weight is exactly zero were still
evaluating an out-of-domain Bessel jet, so the subsequent product formed
``0 * nan``.  The carrier now short-circuits exact zero weights, and the cell
evaluator treats any non-finite returned ball as a domain failure and invokes
the registered whole-box fallback.  The deterministic 24-by-24 born cover
(``seed_grid=12``) is finite again; the seven K4 carrier/integrator regression
suites pass (24 tests in the centred/K4 selection).

This repair changes no budget, partition, or theorem statement.  It is a
design-layer hygiene fix only.  The endpoint 1,152-cell smoke remains a
strictly subunit feasibility result, not a production transcript; the regular
delta=0 patch, global delta cover, weighted union, and independent rerun are
still required before K4 or S1'''/S2''' can be promoted.

## Clean-tree local transcript witnesses (2026-07-17)

The centred integrator was then frozen on two positive-delta bands using the
current dependency hashes. Production and independent replay are byte-identical;
the validator recomputes all seven totals from every recorded terminal cell:

```text
k4_0030: delta=[0.0300,0.0305], 9216 cells, all seven fractions < 1
k4_0040: delta=[0.0400,0.0405], 2304 cells, all seven fractions < 1
```

The artifacts are `surface_remainder_k4_k4_0030.txt` and
`surface_remainder_k4_k4_0040.txt` with their `_rerun` companions, validated by
`validate_surface_remainder_k4_centered_band.py`. These are local witnesses
only: no regular-endpoint patch, remaining delta cover, `t`-union, overlap, or
global S1'''/S2''' judge has been supplied, so `NO_K4_PROMOTION` remains in force.

## Positive continuation (2026-07-19)

The isolated successor campaign on `[0.0305,0.05]` now has all 39 adjacent
rational bands validated in production and replay.  Its aggregate is 89,856
terminal cells with worst normalized fraction `0.501618819006`; provenance is
recorded in
`run-manifests/surface-remainder-k4-positive-0305-0500-20260719.json`.
This is a local positive-delta candidate result only.  The regular endpoint,
the `t`-union, overlap with the regular-ball patch, and literal S1'''/S2'''
weighted judges remain open, so K4 and G6 remain unpromoted.

On 2026-07-24 the 39 pairs were re-audited against the current worktree and
given a separate current-head provenance manifest,
`run-manifests/surface-remainder-k4-positive-0305-0500-current-20260724.json`.
The current union has the same 89,856 cells and worst fraction
`0.501826306922418`; this is a provenance repair only and remains local
candidate evidence with `promotion: NONE`.

The independent t-box chain has also received a current-head manifest,
`run-manifests/surface-remainder-k4-tbox-current-20260724.json`, covering
15 adjacent units and 34,560 cells on `t\in[3,\pi]` at the registered delta
band.  Its replay and local fraction checks pass, but it does not close the
delta union, regular-ball overlap, or the weighted global judge.

## `t`-union design audit (2026-07-19)

An early (t)-diagnostic on the successful positive band `[0.0305,0.031]`
shows that the current fixed-physical integrator is not uniform in `t`: on the
born 576-cell partition the worst normalized fraction ranges from
`3.23e15` at `t=0.8` to `301.1` at `t=3.12`, while the 2,304-cell `t=2.9`
band is below one only after heavy refinement.  The full negative result and
its exact configuration are recorded in
`incidents/INC-K4-T-DESIGN-ENDPOINT-20260719.md`.  No (t)-union production
is authorized from the local positive transcripts; a `t`-dependent regular or
mirror majorant is required first.

## Pre-registered lower contraction-boundary probe (2026-07-20)

Before reading any new output, the research lane freezes one isolated band
immediately below the manifested centred cover:

```text
unit       = k4_00295_0030
delta      = [59/2000, 3/100] = [0.0295,0.0300]
t          = 29/10
seed_grid  = 12
max_cells  = 9216
precision  = 140 Arb bits
```

The separate driver is
`scripts/certify_surface_remainder_k4_centered_00295_0030.py`, with a
production/replay wrapper and validator of the same name. It reuses the
frozen centred integrator without editing the manifested `k4_0030` driver,
and records its own wrapper hash in every transcript. A successful run
requires production and an independent byte-identical replay, finite cell
values, all seven literal carrier fractions strictly below one, dependency
hash agreement, and the validator pass. A failure is retained as an incident
and fixes no gate.

This probe has one purpose only: locate the lower contraction boundary needed
by a future hybrid K4 architecture. It is not a regular-ball patch, does not
cover `(0.01,0.0295)`, supplies no `t`-union or overlap theorem, and must not
alter `NO_K4_PROMOTION`, G1, G2, or G6.

The preregistered band was executed with production and an independent replay:
both contain 9,216 terminal cells, 268 fallback cells, and the validator passes.
The seven normalized carrier fractions are all below one; the largest is
`nuD_main = 0.275772063752004...`.  The candidate manifest is
`run-manifests/surface-remainder-k4-centered-00295-0030-20260720.json`.
This is only a local contraction-boundary witness.  It supplies no regular
ball, overlap, `t`-union, or global S1'''/S2''' judge, so `NO_K4_PROMOTION`
remains unchanged.

## Parameter-variation diagnostic (2026-07-21; no promotion)

The centred integrator was sampled on the registered band
`delta=[1/25,81/2000]` at several fixed `t` values. At the 576-cell
partition, `t=2.9` is subunit in all seven literal fractions, while `t=2.2`
and `t=3.1` fail different carrier families. Refinement to 2,304 cells makes
`t=3.1` subunit and leaves only `MD2r_mirror=1.476` at `t=2.2`; a 9,216-cell
run lowers the latter to `0.287951` and all seven rows become subunit.

These measurements are exploratory calls without production/replay
transcripts, so they are not evidence for a `t`-union. They establish an
implementation boundary: a uniform `t` certificate cannot reuse the 576-cell
stress partition, and a future parameter-jet driver must retain `t`
derivatives before spatial absolute values are taken. The centred carrier
module now preserves a supplied `TJet` in its main and mirror carriers;
`tests/test_surface_remainder_k4_tjet_support.py` guards this behaviour. This
is infrastructure only: K4, S1'''/S2''', G2, and G6 remain unpromoted.

## Certified candidate `t`-box (2026-07-21; no promotion)

The diagnostic window was rerun with the production/replay driver on the full
9,216-cell partition, for `delta=[1/25,81/2000]` and
`t=[11/5,111/50]`. Both transcripts pass the validator and are byte-identical.
Every one of the seven literal carrier fractions is strictly below one; the
largest is `MD2r_mirror=0.503333970406320...`. The two transcripts have SHA-256
`994e62e6cff74680b3ee1168eba326b0f542bbf42e80c16d239c1b282cdf5089`.

This is recorded as
`run-manifests/surface-remainder-k4-tbox-delta0040-t220-222-20260721.json`.
It is a single closed parameter box, not a `t`-union: the regular-ball
construction, overlap argument, literal weighted judges, and the remaining
delta domain are still absent. Therefore `NO_K4_PROMOTION`, G2, G6, and the
global S1'''/S2''' status are unchanged.

## Candidate 39-band rerun (2026-07-22; still no promotion)

The preregistered positive campaign was independently aggregated again after
refreshing `k4p_00`. All 39 adjacent bands on `[61/2000,1/20]` have
production/replay agreement, 89,856 terminal cells, and seven literal
fractions below one. The current worst fraction is
`nuD_main = 0.501826306922...` on `k4p_00`. The manifest is
`run-manifests/surface-remainder-k4-positive-0305-0500-20260719.json`.
This remains a centred-delta candidate only: it supplies no regular-ball
construction, overlap theorem, t-union, or global weighted S1'''/S2''' judge,
and therefore does not alter `NO_K4_PROMOTION` or G6.

## Candidate continuation `[3.08,3.09]` (2026-07-23)

The fixed 2,304-cell centred probe was extended to `t=[77/25,309/100]`.
Production and replay are byte-identical and all seven literal carrier
fractions remain strictly below one; the largest is
`nuD_main = 0.141516484658933...`.  The artifact is
`run-manifests/surface-remainder-k4-tbox-delta0040-t308-309-20260723.json`.
This is still a single-box witness: it does not supply the regular-ball
construction, the overlap theorem, a global `t`-union, or the weighted
`S1'''/S2'''` relay, so K4 and G6 remain unpromoted.

The same fixed probe then passed on `[3.09,3.10]` and `[3.10,3.11]`, each with
2,304 cells and byte-identical replay.  Their worst `nuD_main` fractions are
`0.145991692793684...` and `0.150579541853737...`, respectively.  They are
recorded by the two `surface-remainder-k4-tbox-delta0040-*20260723.json`
manifests and remain single-box candidates; no global K4 or G6 consequence is
drawn.

The same fixed probe then passed on `[3.11,3.12]` and `[3.12,3.13]`, with
worst `nuD_main` fractions `0.155447508897395...` and `0.160398895014984...`.
Both are 2,304-cell, byte-identical production/replay candidates. The
regular-ball, overlap, global `t`-union, and weighted `S1'''/S2'''` proof
obligations remain unchanged.

The final two endpoint boxes `[3.13,3.14]` and
`[3.14,31415927/10000000]` also pass the same 2,304-cell protocol.  Their
worst `nuD_main` fractions are `0.165518753185458...` and
`0.144975893585057...`.  This completes only the local centred candidate
partition up to the conservative pi upper bound; it is not the missing
regular-ball or global weighted K4 certificate.

The executable candidate-union audit
`scripts/audit_surface_remainder_k4_tbox_candidate_union_20260723.py` now
checks all 15 adjacent boxes, 34,560 cells, dependency hashes, and replay
equality from `t=3` to `31415927/10000000`. It reports worst local fraction
`nuD_main=0.165518753185458...`; its scope is explicitly candidate-only.
