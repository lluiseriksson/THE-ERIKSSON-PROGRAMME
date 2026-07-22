# Surface Theorem closure gates

**Status date:** 2026-07-22
**Submission state:** `DO_NOT_SUBMIT`

## Current checkpoint (2026-07-22)

The executable final-seal audit was rerun from the current tree.  It remains
red for the same mathematical reasons, not because of typesetting:

```text
FINAL-SEAL BLOCKED: DO_NOT_SUBMIT manuscript banner
FINAL-SEAL BLOCKED: G2 requires CERTIFIED, found REGULAR_008_AND_HYBRID_009_CERTIFIED
FINAL-SEAL BLOCKED: G6 requires SEALED, found BLOCKED
FINAL-SEAL BLOCKED: amber evidence label
FINAL-SEAL BLOCKED: pending relay language
FINAL-SEAL BLOCKED: unresolved [SLOT] marker
```

The strict finite-beta relay audit currently reports 289 admissible manifested
units, eight beta gaps (including `[765/16,69]`), `promotion: NONE`, and
`relay_status: RELAY_LEMMA_UNPROVED`.  The candidate-topology audit reports
642 paired intervals with one remaining gap `[1629/16,1000/9]`; the three
new pilot cells are explicitly nonterminal and therefore remain quarantined.
The finite-bridge splice identity check passes algebraically (common scaling
and seam geometry), but it proves no sign, tail bound, or G2 relay.

An isolated replacement lane has now been preregistered for the first gap:
`[765/16,193/4]`, CWIN=`3/2`, beta/t Taylor orders `20/25`, 180-bit Arb.
Its production/replay pair contains 198 adjacent strict-negative rows and
passes the independent unit validator.  The pair is deliberately quarantined
(`surface-scaled-bulk-cwin3p2-mid-765-16-193-4-20260722.json`): it is local
candidate sign evidence only and does not change the G2 state or prove the
relay to `(H_tail)`.

A refined direct K2 stress smoke at `(beta,t)=(20,2.9)` now passes twice at
65536 spatial cells with strict margin `0.002143828817...`; the result is
archived in [`SURFACE-K2-DIRECT-STRESS-PASS-20260722.md`](SURFACE-K2-DIRECT-STRESS-PASS-20260722.md).
It remains a one-point candidate and carries no gate load.

The registered positive-box judge was separately hardened against a zero-
containing pilot `KD` coefficient and now follows the frozen 8→16→24→32
mesh ladder.  A representative positive box nevertheless exceeded the
900-second budget without a terminal margin; this is recorded as
[`INC-K2-DIRECT-BOX-TIMEOUT-20260722.md`](incidents/INC-K2-DIRECT-BOX-TIMEOUT-20260722.md)
and does not alter G2.

The current-hash K4 endpoint witnesses also include a two-box strip
`delta=[0.048,0.05]` at `t=2.9`; its seven summed budget fractions are all
strictly below one (worst `nuD=0.7995617222...`).  This remains local
candidate evidence and is not the global K4/S1'''/S2''' union.

The broader K4 candidate audits also rerun green: six centered lower units
(55,296 cells, worst `nuD=0.5101086241...`) and 39 positive-band units
(89,856 cells, worst `nuD=0.5016188190...`).  Both validators explicitly
retain `CANDIDATE ONLY` and therefore do not change K4 or G6.

The preregistered regular-ball reach probe now falsifies its crude complex
hyperbolic-sine modulus: `M_nuD ~ 7.5e321` and the best `N<=16` second-
derivative Cauchy tail is `~9.3e318`, versus headroom `0.3621`.  This is a
terminal design incident for that modulus architecture, not a theorem
disproof; the missing K4 certificate still requires a sharper complex
modulus, moving-tail derivatives, and t-uniformity.

The preregistered signed-bilinear K2 endpoint lane was also rerun with a
parallel driver.  Two fresh runs cover all 158 adjacent born `t` boxes on
`delta=[0,1/1000]` at the frozen grid 48; both structural validators pass and
the complete transcripts are byte-identical (SHA-256
`ED7F46A571377DC71B390E0AB90274B541C1BD631654BBBF2FF1E204FE0A1EEA`).  This
is deterministic same-source candidate evidence only: the exact
`B(0)=0`/denominator audit now passes separately, but the remaining K2
remainder obligations and finite-beta relay are still open, so it does not
promote K2 or G2.

The pair mean-value candidate archive also gained the next dyadic cell
`[13057/128,13058/128]` at `lambda=[3/2,19/10]`; production/replay and its
one-cell manifest audit pass with strict upper endpoint
`-3.0391945389e-109`.  This is a right-edge candidate cell only and does not
repair the bulk beta gap or the sign-to-`H_tail` relay.

The preregistered four-cell continuation immediately above it also passes:
`beta=[13059/128,13063/128]`, four exact adjacent cells, all production/replay
pairs byte-identical, with upper endpoints from `-2.92e-109` down to
`-2.75e-109`.  It remains a right-edge candidate cover, not a G2 certificate.

The direct-sign architecture was probed one lambda cell farther on
`[19/10,2]`; production/replay pass with upper endpoint
`-8.9294764e-109`.  The next wide cell `[2,3]` fails the interval sign judge,
so this route requires narrower lambda subdivision.  These results are
archived as candidate-only artifacts and do not alter G2.

The logical relay audit in
[`SURFACE-FINITE-W-SIGN-RELAY-LOGICAL-AUDIT-20260722.md`](SURFACE-FINITE-W-SIGN-RELAY-LOGICAL-AUDIT-20260722.md)
confirms that a future exhaustive strict `W^J<0` cover could replace
`H_tail` on the matching compact finite-beta domain, provided the manuscript
role audit and domain split are explicit.  The present candidate rows do not
meet that exhaustive-cover condition, so G2 is unchanged.

Earlier broad bounded requests for an analytic global proof of the Wronskian
sign through Bessel monotonicity/total positivity/bridge methods timed out.
A later short Fable High request did return a verified model response; its
logical memo is recorded in
[`SURFACE-FINITE-W-SIGN-RELAY-LOGICAL-AUDIT-20260722.md`](SURFACE-FINITE-W-SIGN-RELAY-LOGICAL-AUDIT-20260722.md),
but it supplies no exhaustive cover and therefore no new theorem claim is
inferred.  K4 endpoint validators also currently reject their stored
manifests because their dependency hashes drifted; this is an audit failure,
not terminal K4 evidence.

This board separates maintenance, local analytic hypotheses, global relay coverage,
and the final editorial seal. Passing one row never promotes another row implicitly.
The authoritative mathematical statement remains
`papers/surface-complete/surface_theorem_complete.tex`.
The current remainder-localization constants and failure rules are pre-registered in
[`SURFACE-REMAINDER-PREREG.md`](SURFACE-REMAINDER-PREREG.md).
The strict release gate is executable as
[`scripts/audit_surface_final_seal.py`](../scripts/audit_surface_final_seal.py);
it is intentionally red while any terminal gate or manuscript slot remains
open.
The manifested L1/L2 localized-core result and its explicit limitations are in
[`SURFACE-REMAINDER-L2.md`](SURFACE-REMAINDER-L2.md).
The exact fixed-domain K4 identity and its current non-terminal design status
are in [`SURFACE-REMAINDER-K4-DESIGN.md`](SURFACE-REMAINDER-K4-DESIGN.md).
The inherited full-torus S2 carrier defect and its main-saddle repair contract
are recorded in
[`incidents/INC-S2-FULL-TORUS-CARRIER.md`](incidents/INC-S2-FULL-TORUS-CARRIER.md).
The pre-registered direct joint-remainder alternative to S2''' is
[`SURFACE-REMAINDER-S2-DIRECT-PREREG.md`](SURFACE-REMAINDER-S2-DIRECT-PREREG.md).
Its born endpoint/positive partition and allowed refinement rules are fixed before the
production run in
[`SURFACE-REMAINDER-K2-PARTITION.md`](SURFACE-REMAINDER-K2-PARTITION.md).
After exact extraction of `r4`, the positive-lane delta-four remainder target is
pre-registered in
[`SURFACE-REMAINDER-R5-PREREG.md`](SURFACE-REMAINDER-R5-PREREG.md).
After the manifested next exact head, the strengthened delta-five target is
pre-registered in
[`SURFACE-REMAINDER-R6-PREREG.md`](SURFACE-REMAINDER-R6-PREREG.md).
After the manifested exact `r6` head, the conditional delta-six target is
pre-registered in
[`SURFACE-REMAINDER-R7-PREREG.md`](SURFACE-REMAINDER-R7-PREREG.md).
Its manifested point-smoke result and explicit limitations are recorded in
[`SURFACE-REMAINDER-S2-DIRECT-STATUS.md`](SURFACE-REMAINDER-S2-DIRECT-STATUS.md).
An alternative exact finite-beta splice, registered before its first scaled
box result, is specified in
[`SURFACE-FINITE-BETA-BRIDGE-PREREG.md`](SURFACE-FINITE-BETA-BRIDGE-PREREG.md).
The rejected centre-value/box-derivative hybrid prototype and its two-track
repair are recorded in
[`incidents/INC-K2-T-CENTER-HYBRID-JET.md`](incidents/INC-K2-T-CENTER-HYBRID-JET.md).
The terminal per-box accounting and deterministic spatial refinement ladder
are fixed in
[`SURFACE-REMAINDER-K2-PRODUCTION.md`](SURFACE-REMAINDER-K2-PRODUCTION.md).
The right-edge paired-sum diagnostic and its explicit finite-mode limitation
are recorded in
[`INCIDENT-G2-PAIR-SUM-EDGE-20260720.md`](INCIDENT-G2-PAIR-SUM-EDGE-20260720.md).

| Gate | Scope | Current state | Terminal evidence required |
|---|---|---|---|
| G0 | v88 numerical sanitation, T1--T7 | `PASS` | five independently rerun authoritative outputs, six nonempty run manifests including T1, reciprocal supersession, and green executable audit |
| G1 | optional local mirror refinement `(H_cube)` | `REMOVED_FROM_TERMINAL_PAPER` | the preceding manuscript step already proves the mirror bound `M` unconditionally and the optional `M_sharp` subsection explicitly carried no relay load.  A static audit now requires `H_cube`, `M_sharp`, and the conditional subsection to be absent while retaining unconditional `M` and its corollary.  K4 remains a documented research lane but is not a theorem or submission gate |
| G2 | analytic bulk tail `(H_tail)` | `REGULAR_008_AND_HYBRID_009_CERTIFIED` | the regular lane independently derives exact `T`, `r2`, `r3`, `r4`, `r5`, and `r6`; eight manifested production segments close `[0,1/125] x [0,pi]` on all 158 born `t` boxes using four incremental core boxes, eight annulus births, physical split `1181/1000`, band radius `66/5`, a frozen mixed `384/192/384` grid map, and worst strict lower margin `0.0000111964` at index 50, absorbing positive births 1--7; the hybrid birth `[1/125,9/1000]` now has a current-head 158-unit union validator from commit `8b4a17c0681601d0d433ed769d23ce8daa8269a9`, with worst strict lower margin `0.0169551281` at `parent_145`, and is owned by `run-manifests/surface-remainder-k2-hybrid009-current-20260717T085239Z.json`.  This closes only the regular part; the moving-edge complement is assigned to G5.  The exact finite-beta bridge is preregistered as an alternative to all 42 later delta births: scaled direct certificates would cover `20<=beta<=1000/9`, then splice exactly to the current regular lane.  It has no theorem load until its scaled-tail contract and exhaustive unions pass |
| G3 | compact relay `[6,20]` | `CERTIFIED` | two bivariate beta/t Taylor Arb covers: 179 contiguous beta boxes, 7,958 strict t boxes, transcripts + manifests + executable coverage validators |
| G4 | left edge `t in (0,0.6]` | `CERTIFIED` | `[3,20]` is closed by the manifested `W/t^3` + ordinary Taylor splice.  For `20<=beta<=1000/9`, the exact scaled paired-moment bridge through `t^16` uses the fixed `19/100` splice: 912/912 atomic production intervals and 4,636 rows pass the grouped coverage/sign validator, and a fresh independent grouped replay reproduces all 912 intervals and 4,636 rows exactly after parsing.  The production and replay transcripts carry the same frozen head and dependency hashes.  The infinite Fourier-tail contract is audited in `SURFACE-FINITE-BETA-BRIDGE-TAIL-CONTRACT.md` and `verify_surface_scaled_tail_contract.py`.  This closes G4; it does not close the scaled bulk, K2, K4, or G6. |
| G5 | moving right edge | `CERTIFIED` | the manifested compact union closes `3<=beta<=20`.  The relocated-splice design continues to beta 25, but the fixed diagnostic band `[1/25,1/20]` for `20<=beta<25` fails at the adversarial endpoint (`H_lower=-0.178827...`; see `INC-G5-BETA20-25-ENDPOINT.md`); that rejected route is not used.  The preregistered cached compact extension closes `[20,25]`: four frozen units, 721/721 beta boxes, 18,659 regular boxes, production validation and a fresh replay agree exactly, with frozen dependency hashes and configuration.  The lower finite bridge has authoritative production plus fresh independent replay: 225/225 rows on `25<=beta<=30`, exact row equality, worst `H` lower `0.0199195495...` at `(2,74)`.  The upper finite bridge now also has production plus fresh independent replay: 375/375 rows on `30<=beta<=125`, exact row equality, worst `H` lower `0.0258956127...` at `(3,74)`.  For `beta>=125`, exact divided differences reduce the target to five scaled families with `H=P0/(4 B0^2)`: all 600 frozen design cells and all 600 production cells from source commit `1da7e414` pass, and the union validator gives worst `H` lower `0.0538267940...` at `(0,74)`.  The independent rerun reproduces all 600 rows byte-for-byte after JSON parsing from that same commit.  The order-only validator incident is documented without changing transcripts.  G5 is closed; the scaled bulk, K2, K4, and G6 remain open. |
| G6 | global theorem and paper seal | `BLOCKED` | G0--G5 terminal, all manuscript `[SLOT]` markers removed by proved/certified text, full build, citation audit, and independent claim audit |

The unscaled compact G4 engine is not a viable half-line substitute.  A post-certificate
extension attempt on the first box `[20,20.1]` consumed more than 15 CPU
minutes without completing, versus seconds per box lower down, and was
terminated without a result.  No claim or transcript was produced.  That
negative result applies to direct use of exponentially large `I_m(beta)`.
The newly preregistered finite bridge instead uses the exact common scaling
`J_m=exp(-beta)I_m`, under which `W_scaled=exp(-8 beta)W`; it is a distinct
architecture and remains design-only until its pre-registered probes run.

The `[20,30]` scaled-bulk candidate now has a separate production/replay
union (100 beta boxes, 11,754 adaptive `t` boxes), and the independent
derivative-tail audit passes at beta lower endpoints 20, 25, and 30.  This is
still only a partial candidate: it has no load on G2 or G6 until the remaining
`[30,1000/9)` union and the full sign contract are independently closed.

A static audit on 2026-07-16 (`scripts/audit_surface_scaled_bulk_transcript_rows.py`)
independently parsed the two archived units: both `[20,25]` and `[25,30]`
contain 50 adjacent beta rows, and each replay has byte-identical `beta-box`
rows to production (first/last endpoints `20.0--25.0` and `25.0--30.0`).
This checks transcript integrity only; it does not replace the missing
`[30,1000/9)` union, the scaled-tail contract, or the theorem-level promotion
review.

## Promotion rules

1. `VERIFIED` means a deterministic non-interval computation reproduced from a
   manifested command; `CERTIFIED` means outward-rounded interval evidence with its
   exact script and inputs manifested. Design numerics receive neither label.
2. Every generated transcript added or changed after the evidence gate must be owned by
   exactly one run manifest. A script hash printed by a transcript must match the
   executed-byte hash or a declared portable LF hash.
3. Comparison against historical evidence uses absolute differences. Relative
   differences may be printed only as secondary diagnostics and must be marked near zero.
4. A rerun that starts from the wrong working directory, misses an input, scans zero
   targets, or exits before its verdict is failed evidence even if earlier lines look
   plausible.
5. G1 and G2 share an implementation architecture but are separate mathematical judges.
   Neither discharges G3--G5.
6. G6 cannot be inferred from a paper build. The build checks typesetting; the gate checks
   that every claimed range is proved or certified.

The derivative convention is fixed by the order-one Taylor formula and the final v86
judges: S1''' and S2''' use `v_m''` and `Y''`. The quadruple-prime notation in the older
v84 design paragraph is not a fourth-derivative requirement and must be amended before
production text is promoted.

## Current measured remainder direction

The first-order fixed-box and centered-form approaches are too wide at the registered
stress cell. A design-only degree-three spatial Taylor model, with the quadratic
polynomial integrated exactly against the affine phase, contracts below the
pre-registered delta-six budget at the stress point after the companion charge.  This
is still not an S1''' or S2''' certificate: a first attempt to add a whole `t` box mixed
centre values and box derivatives before nonlinear assembly and was rejected.  The
live repair integrates the spatial Taylor polynomial through degree four, charges the
total-degree-five remainder, carries separate centre/whole-box parameter jets through
order four, and applies Taylor only after the two quotient assemblies.  Its uniform
sum is deterministically split into contiguous spatial row slices; the 64-cell parallel
smoke reproduced the sequential enclosure exactly.  It does not yet cover the born positive partition,
treat the completion, or cross `delta=0`. Its next promotion condition is a finite,
adversarially tested literal weighted-sum driver with every auxiliary charge, not a
larger unmanifested numerical run.

The inherited phrase “full-plane chart integral of the true untruncated integrand” is
not yet a definition suitable for certification: the literal trigonometric integrand is
periodic and repeats saddles on the full scaled plane. Before S1''' or S2''' can be
claimed, the implementation must specify either a fixed physical-domain formulation or
an explicit fixed-domain localization/cutoff. In the latter case, the complementary
piece must include the cutoff's value, first, and second `delta` derivatives. No code may
silently integrate a moving scaled rectangle while differentiating only its integrand.

### Latest route audit (2026-07-16)

The preregistered scaled moving-bulk localization was executed without beta
bisection: the order-11 box `[60,60.1]` failed first near
`t=2.5470737520174302`, and the authorized fallback `[50,50.1]` failed near
`t=2.7584514361433383`. These are design-level falsifications of that route,
not G2 or theorem failures. The finite-beta bridge remains without theorem
load, and the K4 endpoint convergence/transport oracles remain explicitly
local until a global union and independent production rerun exist.

## Automation order

1. complete G0 and close the T1 incident at the evidence level;
2. turn the second-order remainder prototype into a small falsifiable S1''' stress-cell
   smoke, then add K2/K4 before any global claim;
3. implement G1 and G2 as separate machine-readable verdicts;
4. G3 is closed by the manifested bivariate-Taylor series certificate; preserve the
   exp-factored local box as an independent mechanism audit;
5. fabricate G4 and G5 with independent edge-specific certificates;
6. enable a final seal check that rejects `[SLOT]`, `DO_NOT_SUBMIT`, open hypotheses, or
   nonterminal gate states.

The K4 low-z mirror probe also exposed and repaired a genuine interval
positivity loss in the centred square-root jet: reconstructing the positive
value enclosure of (r^3) from its endpoints removes a spurious zero crossing
and restores finiteness on the witness cell. This is recorded as
`LOW_Z_SQRT_REPAIR_LOCAL`; the seed-48 sweep is finite but its worst normalized
fraction is (8.2781\times10^{17}), so K4 remains design-only and G6 remains
blocked.

The scaled-bulk design was extended beyond the original `[20,30]` probe:
the CWIN=3/2 `[30,31]` block passes 10 beta boxes (3,809 adaptive `t` boxes),
while the separately manifested CWIN=4 `[31,35]` candidate passes 40 boxes
(19,019 adaptive `t` boxes). A width-one request at beta 35 is automatically
narrowed through `1/2`, `1/4`, and `1/8`, confirming that these are exploratory
routes rather than terminal G2 certificates. The CWIN=4 strips are archived in
the three candidate manifests for `[31,35]`, `[35,36]`, and `[36,37]`; none has
G2/G6 promotion load.

The high-order `CWIN=3/2` successor `[78+1/8,78+1/4]` was then run under the
pre-registered order-30/order-37, 180-bit contract.  It produced 189 adjacent
terminal rows with strictly negative Arb upper endpoints; the compact
provenance record is `scripts/surface_scaled_bulk_cwin3p2_high_78p125_78p25_run.txt`.
An independent replay of the same unit reproduced the domain and row count.
This remains candidate evidence only: it does not promote G2/G6 or discharge
the missing union and scaled-tail splice.

An independent continuation probe at `[67,67.5]` was also stopped by the
fixed 240-second operational budget after the backend narrowed its beta step
from `1/2` to `1/4` and then `1/8` at the first endpoint.  The initial
derivative-overlap smoke passed, but no terminal interval or sign union was
produced.  This conditioning/cost boundary is recorded in
`INC-SCALED-BULK-67-DESIGN-TIMEOUT.md`; it adds no G2 or G6 load and leaves
`[67,1000/9)` open.

The preregistered successor `[67,67.25]` now has a sign-row production and
byte-identical replay: 189 adjacent terminal `t` intervals, every recorded
Arb upper endpoint strictly negative, under `beta_order=24`, `t_order=29`,
and `CWIN=4`.  Its contract is `SURFACE-SCALED-BULK-67-67P25-PREREG.md` and
the executable validator is
`validate_surface_scaled_bulk_67_67p25.py`.  This remains candidate-only and
does not change G2/G6; the full `[67,1000/9)` union, tail contract, and relay
promotion are still missing.

The same contract has been extended to `[67,67.5]` with two adjacent beta
boxes.  Production and replay agree on 379 terminal `t` rows, each with a
strictly negative Arb upper endpoint and complete per-box adjacency.  The
extension is recorded in `SURFACE-SCALED-BULK-67-67P5-PREREG.md`; it remains
candidate evidence only and does not alter G2/G6 because
`[67.5,1000/9)`, the tail splice, and the relay audit remain open.

The following four-box strip `[68,69]` is likewise production/replay green:
777 terminal `t` rows, strict negativity on every row, and exact adjacency in
each beta box.  Its contract is `SURFACE-SCALED-BULK-68-69-PREREG.md` and its
validator is `validate_surface_scaled_bulk_68_69.py`.  This is still candidate
evidence only; `[69,1000/9)`, the scaled-tail splice, and G2/G6 promotion are
not closed.

The frozen 169-box campaign after `69` has started with a complete `[69,70]`
batch: 4/4 beta units, 796 terminal `t` rows, exact production/replay
agreement, and a green partial validator.  The remaining units through
`1000/9` are not yet run, so this batch carries no G2/G6 promotion.

Within the next batch, parent `[70.75,71]` (`69_007`) failed at the frozen
quarter width near the moving edge.  Its separately preregistered two-half
repair now passes production/replay and validation with 386 terminal rows;
the parent is not counted as evidence, and the remaining campaign is still
open.

The next parents `[71,71.25]` and `[71.25,71.5]` also require explicit fixed
half-width repairs; their validators pass with 389 and 390 rows.  These
repairs are canonicalized by exact beta intervals and do not grant further
adaptive bisection.  The repeated edge conditioning confirms that the
`CWIN=4` campaign remains candidate evidence only.

An isolated local probe with the relay-required `CWIN=3/2` at
`beta=[69,69.25]` fails near `t=3.11444315` under the same order-24/order-29
backend.  The incident is `INC-SCALED-BULK-CWIN-3P2-LOCAL-FAIL-20260717.md`;
the CWIN=4 candidate cannot be promoted by relabelling its boundary.

A separately preregistered narrow-seam probe then subdivided that same beta
domain into four immutable width-`1/16` descendants.  Production and replay
are byte-identical, with 747 adjacent terminal `t` rows and strict negative
Arb upper endpoints.  This candidate witness is recorded in
`SURFACE-SCALED-BULK-CWIN3P2-NARROW-PREREG.md`; it carries no G2/G6 load until
the complete finite-beta union, scaled-tail splice, and independent relay
audit are closed.

The same pre-registered partition has now been extended to the adjacent
`[69.25,69.5]` domain.  All eight units together replay exactly and validate
1,496 strict rows.  This remains candidate evidence only; it neither closes
the unrun interval nor removes the scaled-bulk slot.

The fixed-width extension `[69.5,70]` is also green for all eight descendants.
The sixteen-unit prefix `[69,70]` therefore validates 3,008 strict rows with
exact production/replay equality.  It remains a candidate prefix only and
does not alter G2/G6.

The conditioning boundary near β=100 has an independent high-order candidate
unit `[100,100+1/16]` under `beta_order=30`, `t_order=37`, and 180 Arb bits.
Its production/replay pair and executable validator accept 300 strict rows.
This is a separate candidate architecture, not a promotion: the full
finite-beta union, tail splice, and relay audit remain open.

The exact adjacent unit `[100+1/16,100+2/16]` was then preregistered under the
same `CWIN=3/2`, order-30/order-37, 180-bit contract.  Production and an
independent replay agree on 301 strict rows, and
`validate_surface_scaled_bulk_cwin3p2_high_100p0625.py` passes.  This is still
candidate evidence only; no G2/G6 load is assigned until the complete union,
scaled-tail splice, and relay audit exist.

The following exact unit `[100+1/8,100+3/16]` was preregistered before running
and independently reproduces 302 strict rows under the same contract.  The
generic validator checks the rational endpoints and the complete production /
replay equality.  The out-of-contract trial with upper endpoint `803/8` is
quarantined in `INC-SCALED-BULK-HIGH-100P125-CLI-DOMAIN-20260717.md`; neither
run changes G2/G6.

The next adjacent unit `[100+3/16,100+1/4]` also passes production and replay
with 302 strict rows under the identical contract.  This is candidate evidence
only; it supplies no G2/G6 load without the full finite-beta union, tail splice,
and relay audit.

A provenance-bearing partial candidate for `[35,36]` is now frozen separately
with beta width `1/8`. Production plus replay and the executable validator
pass for eight adjacent boxes and 6,344 adaptive `t` boxes. It remains a
candidate witness only: it does not extend G2, discharge the interval
`[36,1000/9)`, or remove the manuscript slot.

The K4 direct fixed-domain probe now also passes finiteness on all 576 born
cells at the stress point after extending the scaled-Bessel outer derivatives
with the positive entire series and repairing the TJet reciprocal branch.
This is recorded as `LOW_Z_DIRECT_ENTIRE_LOCAL`; no K4 coefficient, tail, or
global S1'''/S2''' union is promoted.

The endpoint successor then passes a frozen two-box weighted strip at
`t=2.9`: `[0.048,0.049]` on 2,304 cells plus `[0.049,0.05]` on 1,152 cells;
all seven totals are strict, with worst normalized total `0.7989012329`.
Its transcript/validator pair is
`surface_remainder_k4_endpoint_strip_transcript.txt` /
`validate_surface_remainder_k4_endpoint_strip.py`.  This local witness does
not alter `NO_K4_PROMOTION` because the low-`z`, full-`t`, overlap, and global
S1'''/S2''' obligations remain open.

The clean-tree centred-delta successor now has two local transcript pairs:
`k4_0030` covers `[0.0300,0.0305]` with 9,216 terminal cells and `k4_0040`
covers `[0.0400,0.0405]` with 2,304 cells. Production and replay are
byte-identical, and the executable validator recomputes all seven totals with
strictly subunit normalized fractions. These witnesses do not change the gate:
the regular endpoint, the remaining delta/t union, overlap, and global
S1'''/S2''' assembly are still absent.

An order-13 (t)-Taylor candidate for `[36,37]` is also
production/replay-validated: eight adjacent beta boxes and 1,258 adaptive
`t` boxes agree exactly. It is partial evidence only and leaves the global
scaled-bulk slot open.

The order-17 candidate was then extended to `[37,40]` under a frozen
`CWIN=4`, beta-order-12, `(t)`-order-17 contract. Production and independent
replay agree exactly on the complete adjacent union: 32 beta boxes and 3,151
adaptive `t` boxes. The unit `[39,40]` encountered the preregistered failure
witness and therefore refined from width `1/8` to `1/16`; both transcripts
contain the literal witness and the validator rejects any other partition.
This remains candidate evidence only: `[40,1000/9)`, the analytic splice, and
the global sign/relay audit are still open, so G2 and G6 are unchanged.

High-beta diagnostics are now separately recorded in
`INC-SCALED-BULK-HIGH-BETA-COST-20260716.md`: order 24 closes one local box at
beta 60, while beta 80 does not reach a terminal verdict within the fixed
15-minute operational budget, even after moving `CWIN` to 8. These are cost
boundaries, not sign certificates, and do not alter G2/G6.

The same order-17 candidate was independently extended to `[40,43]` under a
separate preregistration.  Production and replay agree exactly on 48 adjacent
beta boxes and 5,646 adaptive `t` boxes; each of `[40,41]`, `[41,42]`, and
`[42,43]` uses the registered `1/16` refinement witness.  This is still
partial candidate evidence only and carries no load on G2 or G6: `[43,1000/9)`
and the global sign/relay and splice audits remain open.

An out-of-contract G5 probe near `lambda=2.8` lost `P0` resolution; an
independent 80-digit 700-mode point sum still gives `W<0`. The incident is
recorded in `INC-G5-LAMBDA-28-EVALUATOR-LOSS.md`; no G5 extension is inferred.

A corrected half-line probe at `lambda in [2.70,2.72]`, with the near and far
tail constants recomputed for that lambda range, has strict local margins
(`B0>0.0831`, `P0>0.000188`, `H>0.00449`). It remains design-only; the finite
beta geometry and the exhaustive seam are still open.

An exploratory order-17 probe of `[43,45]` still passes its local sign cover,
but reaches a new dyadic ceiling: width `1/32` is required after the
registered `1/8` and `1/16` reductions. The result is recorded in
`INC-SCALED-BULK-43-45-ADAPTIVE-CEILING.md`; it has no production provenance
or theorem load and prevents silently extending the `[40,43]` contract.

A preregistered replacement candidate at `[43,45]` raises only the beta
Taylor order from 12 to 16, keeping `CWIN=4`, `(t)` order 17, precision 180,
and beta width `1/8`. Production and replay now agree on all 16 adjacent beta
boxes and 2,269 adaptive `t` boxes (1,095 on `[43,44]`, 1,174 on
`[44,45]`). This repairs the local dyadic ceiling but remains candidate
evidence only; `[45,1000/9)`, the splice, and the global relay audit remain
open, so G2/G6 are unchanged.

The next order-24 candidate contract for `[45,50]` is now registered with
`CWIN=4`, beta order 24, `(t)` order 17, precision 180, and beta width `1/8`.
Its first two production units `[45,46]` and `[46,47]` passed (1,293 and
1,424 adaptive `t` boxes), but the full five-unit launcher exceeded the
15-minute operational budget before `[47,50]` completed.  Those two unit
transcripts remain partial candidate evidence only; no G2/G6 state changes.
An independent exploratory `[47,48]` run also passed 1,537 boxes and is
archived separately, without production or theorem load.
The adjacent exploratory `[48,49]` run also passed (1,642 boxes in 411 s),
but is likewise design-only and leaves `[49,1000/9)` plus the replay union
open.
The final exploratory `[49,50]` unit passed 1,788 boxes in 443 s; it too is
archived as design-only.  The entire exploratory sign strip `[45,50]` is now
positive, but no production union, replay, or tail/relay promotion has been
performed.
One unit has since been promoted to the full protocol: `[47,48]` now has
production plus independent replay, exact equality of all eight beta rows, and
the executable validator (`1,537` adaptive `t` boxes).  This remains a local
candidate witness; the adjacent union and the remaining high-beta splice are
not promoted.

The K2 denominator-sign diagnostic is now regression-tested but remains
isolated.  A pointwise order-six lower envelope gives `K_D >=
0.133835750845...` on the stress box `delta=[0.010,0.011]`, `t=[1,1.02]`
with 4,096 cells, repairing the whole-box interval-dependency loss.  The
joint remainder and sixth-coefficient budget are not certified, so this does
not change G2 or G6.  The formal `r_7,r_8` derivation is likewise archived as
design-only material.

The next central scaled-bulk unit `[30,31]` is now a complete local candidate:
the frozen `CWIN=4`, order-12/order-9, 180-bit production and replay have
identical provenance and 10 adjacent beta rows (2,827 adaptive `t` boxes).
The independent validator passes.  An earlier exploratory count of 3,809
boxes used the legacy `CWIN=3/2` default and is quarantined in
`INC-SCALED-BULK-30-31-CWIN-DISCREPANCY.md`; only the 2,827-row contract is
admissible.  This unit remains candidate evidence and does not change G2/G6:
the union `[30,1000/9)` and the scaled-tail promotion are still open.

The frozen `[31,35]` continuation has now also completed production and fresh
replay under the same `CWIN=4`, order-12/order-9, 180-bit contract.  Its four
units form 40 adjacent beta rows and 19,019 adaptive `t` boxes; each replay
transcript is byte-identical to production, and the independent union validator
passes.  These are still local candidate witnesses: the remaining central
strip and the global scaled-tail/relay audit are not promoted.

An exploratory order-24 `[50,51]` run was started and aborted before any
terminal row; it produced no evidence and is recorded in
`INC-SCALED-BULK-50-51-ABORTED.md`.  No retrospective refinement or replay is
authorized from that attempt.

The follow-on `[51,52]` preregistration has completed as well: eight order-24/
order-17 units at beta width `1/8`, exact production/replay equality, and a
passing union validator for 2,237 adaptive `t` boxes. It remains candidate
evidence only; no central-bridge or G2/G6 promotion follows from this local
strip.

That aborted probe was superseded by the frozen `[50,51]` preregistration:
eight order-24/order-17 units at beta width `1/8`, with `CWIN=4`. Production
and fresh replay now agree on all eight rows and the independent validator
passes the exact union `50.0--51.0`, totaling 2,015 adaptive `t` boxes. This
is still local candidate evidence; it does not promote the remaining bridge or
G2/G6.

The continuous candidate campaign `[52,60]` is now complete: 64 frozen
order-24/order-17 units, 28,666 adaptive `t` boxes, exact production/replay
equality, and a passing union validator. The larger 16-unit `[54,56]` launcher
timed out before output and is recorded separately; successful reruns used the
same registered contract in four-unit batches. This remains candidate evidence
only and does not promote G2/G6.

An order-24 exploratory probe over `[60,61]` also passed locally (1,571
adaptive `t` boxes, split at beta `60.5`). It is quarantined in
`INC-SCALED-BULK-60-61-DESIGN-PASS.md`: without a frozen production/replay
pair, union validator, and scaled-tail splice it carries no G2/G6 load.

The previously partial `[45,50]` strip is now complete under its frozen
order-24/order-17, `CWIN=4`, beta-width-`1/8`, 180-bit contract: 40/40 beta
boxes, 7,684 adaptive `t` boxes, exact production/replay equality, and a
passing independent union validator. It is still candidate evidence only;
the central `[20,1000/9)` bridge and global scaled-tail promotion remain open.

The next frozen high-beta strip `[60,61]` is also complete: two half-width
units under order 24/17, `CWIN=4`, 180 bits, exact production/replay equality,
and 1,571 adaptive `t` boxes in the independent validator. Its production
transcript hashes are `e45c86874b26ea9c30e836c42439b61b29bb1fb2bd43b3f3a9e07d76fc8ebc18`
and `f1fb52d04e7d86a570c167d326ea1779faeacd1ab5036f87fe3315bb46b1af2c`.
It remains candidate evidence only; no G2/G6 promotion follows.

The continuation `[61,63]` is complete under the same frozen backend: four
input units, seven terminal beta rows after deterministic adaptive refinement,
6,177 adaptive `t` boxes, exact production/replay equality, and a passing
union validator. The adaptive-row validator correction is recorded in
`INC-SCALED-BULK-61-63-ADAPTIVE-ROWS.md`; no production transcript changed.
This block remains candidate evidence only.

The next continuation `[63,65]` is complete as well: eight terminal beta rows,
8,453 adaptive `t` boxes, exact production/replay equality, and a passing
union validator under the same order-24/17, `CWIN=4`, 180-bit contract. It is
still candidate evidence only and carries no G2/G6 load.

The short high-beta block `[65,66]` is complete: four terminal beta rows,
5,146 adaptive `t` boxes, exact production/replay equality, and a passing
union validator under the same frozen contract. It remains candidate evidence
only; the scaled-tail splice and G2/G6 promotion are still open.

The following block `[66,67]` is complete: four terminal beta rows, 5,825
adaptive `t` boxes, exact production/replay equality, and a passing union
validator under the same frozen contract. It remains candidate evidence only.

Re-running every available scaled-bulk union validator now gives 407 adjacent
beta boxes and 120,042 adaptive `t` boxes across the candidate strips
`[20,67]`; every available production/replay pair is green. This aggregate is
an audit summary, not a G2 promotion: the analytic scaled-tail contract and
the final theorem relay are still absent.

The same 17-validator audit is now executable as
`scripts/audit_surface_scaled_bulk_candidate_campaign.py`. On 2026-07-17 it
reproduced all 17 green child verdicts and prints each child hash, then ends
with `AUDIT PASS validators=17/17 CANDIDATE_ONLY` and an explicit
`NO G2/G6 PROMOTION` line. The driver is intentionally non-authoritative and
does not write manifests.

A preregistered CWIN=3/2 continuation for `[69.5,70]` has now completed a
fresh production/replay pair: eight width-`1/16` beta units, 1,512 terminal
`t` rows, exact transcript equality, and an independent validator pass. The
contract and producer are in
`SURFACE-SCALED-BULK-CWIN3P2-69P5-70-PREREG.md` and
`scripts/run_surface_scaled_bulk_cwin3p2_69p5_70.py`. This extends only the
candidate archive; the full `[69,1000/9)` union, tail splice, and relay audit
remain open, so G2/G6 are unchanged.

The immediately adjacent preregistered continuation `[70,71]` is also green:
16 width-`1/16` units, 3,107 terminal `t` rows, exact production/replay
equality, and the independent validator
`scripts/validate_surface_scaled_bulk_cwin3p2_70_71.py`. Its contract is
`SURFACE-SCALED-BULK-CWIN3P2-70-71-PREREG.md`; it remains candidate-only and
does not alter G2/G6.

The next preregistered block `[71,72]` is green as well: 16 width-`1/16`
units, 3,244 terminal `t` rows, exact production/replay equality, and the
independent validator `scripts/validate_surface_scaled_bulk_cwin3p2_71_72.py`.
Its contract is `SURFACE-SCALED-BULK-CWIN3P2-71-72-PREREG.md`; it remains
candidate-only and does not alter G2/G6.

Above β=72 the frozen width can be doubled: the preregistered `[72,73]`
campaign uses eight width-`1/8` units and passes production/replay with 1,741
terminal `t` rows. Its validator is
`scripts/validate_surface_scaled_bulk_cwin3p2_72_73.py`, and the contract
records the rejected width-`1/4` diagnostic. This is candidate-only; G2/G6
remain unchanged.

The adjacent `[73,74]` width-`1/8` campaign is also green: eight units,
1,814 terminal `t` rows, exact production/replay equality, and validator
`scripts/validate_surface_scaled_bulk_cwin3p2_73_74.py`. Its preregistration
is `SURFACE-SCALED-BULK-CWIN3P2-73-74-PREREG.md`; this remains candidate-only.

The five blocks from `[69.5,74]` now have a single aggregate audit driver,
`scripts/audit_surface_scaled_bulk_cwin3p2_69p5_74.py`. It re-runs all five
validators and reports 56 beta units / 11,418 terminal rows before printing
`CANDIDATE ONLY; NO G2/G6 PROMOTION`.

The next width-`1/8` block `[74,75]` is green as well: eight units, 1,880
terminal `t` rows, exact production/replay equality, and validator
`scripts/validate_surface_scaled_bulk_cwin3p2_74_75.py`. Its contract is
`SURFACE-SCALED-BULK-CWIN3P2-74-75-PREREG.md`; the candidate archive now
reaches β=75 without changing G2/G6.

The adjacent `[75,76]` width-`1/8` block is green: eight units, 1,950
terminal `t` rows, exact production/replay equality, and validator
`scripts/validate_surface_scaled_bulk_cwin3p2_75_76.py`. Its contract is
`SURFACE-SCALED-BULK-CWIN3P2-75-76-PREREG.md`; it remains candidate-only.

The next width-`1/8` block `[76,77]` is green: eight units, 2,017 terminal
`t` rows, exact production/replay equality, and validator
`scripts/validate_surface_scaled_bulk_cwin3p2_76_77.py`. Its contract is
`SURFACE-SCALED-BULK-CWIN3P2-76-77-PREREG.md`; it remains candidate-only and
does not alter G2/G6.

The uniform width-`1/8` parent attempt `[77,78]` is **not green**: units
`00`--`03` completed, while unit `04` failed near the right `t` edge. The
failure is retained in `INC-SCALED-BULK-CWIN3P2-77-04-EDGE-FAIL-20260717.md`;
the parent contract is not promoted. Its width-`1/64` rescue for
`[77.5,77.625]` is independently green: eight units, 2,024 terminal rows,
exact production/replay equality, and validator
`scripts/validate_surface_scaled_bulk_cwin3p2_77_04_64_rescue.py`. The rescue
contract is `SURFACE-SCALED-BULK-CWIN3P2-77-04-64-RESCUE-PREREG.md`; it is
candidate-only and does not repair the failed parent block.

The remaining failed parent units `[77.625,78]` have a separate width-`1/64`
rescue that is now complete: 24 units, 6,122 terminal rows, exact
production/replay equality, and validator
`scripts/validate_surface_scaled_bulk_cwin3p2_77_05_07_64_rescue.py`. Its
contract is `SURFACE-SCALED-BULK-CWIN3P2-77-05-07-64-RESCUE-PREREG.md`.
Together with the preceding rescue and the completed replay of parent units
`[77,77.5]`, the mixed-width audit
`scripts/validate_surface_scaled_bulk_cwin3p2_77_78_mixed.py` supplies a
contiguous candidate union through β=78. It remains candidate-only: the
failed uniform parent cells and the analytic full-union/relay obligations
leave G2/G6 unchanged.

The complete candidate archive from `[69.5,78]` now has one aggregate replay
auditor, `scripts/audit_surface_scaled_bulk_cwin3p2_69p5_78_mixed.py`: nine
validated components, 116 beta units, and 26,444 terminal rows. It ends with
`CANDIDATE ONLY; NO G2/G6 PROMOTION`; it is an evidence index, not an analytic
replacement for the missing finite-beta tail contract.

The independent high-beta tail subcontract audit now passes at lower endpoints
`40,50,60,66,80,100,1000/9`, with orders `0..17`, both mode weights, and
strict geometric ratios (worst reported ratio `0.0363826891...` at
`1000/9`). This strengthens only the arithmetic tail majorant; it does not
certify the missing sign union or promote G2/G6.

The parent-width failures in the `[69,1000/9]` candidate campaign continue
through `69_015`. A separate fixed uniform-width-`1/8` route was then tried in
the `u69_000`--`u69_337` transcript namespace. It failed at units
`u69_085`--`u69_098` near the right `t` edge; the retained negative
transcripts and decision to stop are recorded in
`INC-SCALED-BULK-UNIFORM-1_8-FAIL-20260717.md`. No replay, manifest, or
G2/G6 promotion was made. Any replacement route requires a new preregistration
and an analytic explanation of the edge obstruction.

The repository-wide manifest audit also has the documented historical
worktree-drift incident `INC-MANIFEST-WORKTREE-DRIFT-20260717.md`; it remains
an explicit audit failure until those carrier edits receive an honest
supersession or the original dependency snapshots are restored.

An exploratory high-order `CWIN=3/2` continuation at
`[78,78.125]` produced 189 strict sign rows under the driver recorded in
`SURFACE-SCALED-BULK-CWIN3P2-HIGH-78-78P125-DESIGN.md`.  It has no frozen
production/replay pair or manifest and therefore changes neither G2 nor G6.
### 2026-07-18 high-order width audit

The high-order `CWIN=3/2` unit `[78.25,80]` was run under its preregistered
configuration and failed at the minimum `t` width near `1.7801476736942292`;
the failed transcript and rationale are in
`INC-SCALED-BULK-CWIN3P2-HIGH-78P25-80-FAIL-20260718.md`. The narrower unit
`[78.25,78.375]` passed production and independent replay with 189 strict
rows and byte-identical output. Both results are candidate-only: they change
neither G2 nor G6 and do not relax the full-union or tail requirements.
The adjacent unit `[78.375,78.5]` also passed the same production/replay
protocol with 189 rows; the two-unit seam remains candidate-only.
The next `[78.5,78.625]` unit passes the same protocol with 190 rows; this
three-unit seam remains candidate-only and does not alter G2 or G6.

The next preregistered high-order unit `[78.625,78.75]` has now completed
production, independent replay, and byte-level validation (191 strict rows,
with exact transcript equality). It remains candidate-only: until the complete
finite-beta union and the analytic splice are closed, no G2 or G6 promotion
follows from this unit.

The adjacent preregistered unit `[78.75,78.875]` likewise passes production,
independent replay, and byte-level validation (192 strict rows). The four-unit
seam through `78.875` is now checked by
`scripts/validate_surface_scaled_bulk_cwin3p2_high_78p25_78p875.py` (five
adjacent units, 951 rows, exact production/replay equality). It remains
candidate-only and carries no G2/G6 promotion.

The next unit `[78.875,79]` also passes production/replay validation (192
strict rows). The aggregate seam validator now checks six adjacent units and
1,143 rows through `beta=79`; this remains candidate evidence only.

The narrow continuation `[79,79.125]` also passes production/replay validation
(192 strict rows). The same aggregate check now covers seven adjacent units
and 1,335 rows through `beta=79.125`; it remains candidate-only.

The next unit `[79.125,79.25]` passes as well (193 strict rows); the aggregate
then covered eight adjacent units and 1,528 rows through `beta=79.25`. The
high-order tail verifier sees 13 production files and still has worst
contraction ratio `0.0173228687`; neither result changes G2/G6.

The first unit of the previously identified gap, `[79.25,79.375]`, also passes
production/replay validation (193 rows). The local high-order component now
reaches `beta=79.375`; the union audit reports the remaining gap
`[79.375,100]` exactly.

The next unit `[79.375,79.5]` passes the same protocol (193 rows). The paired
component now reaches `beta=79.5`; the executable audit reports the remaining
gap `[79.5,100]`.

The next unit `[79.5,79.625]` also passes production/replay validation (193
rows). The paired component now reaches `beta=79.625`; the remaining audited
gap is `[79.625,100]`.

The isolated order-40/order-45 rescue for the failed wide box `[79.5,80]`
also passes production and replay (405 strict rows). Its dedicated validator
and tail-contract audit pass; the local-union auditor now merges the overlap
and reports 16 paired units, 3,717 rows, one continuous component `[78.25,80]`,
and the remaining gap `[80,100]`. This rescue remains candidate evidence until
the complete finite-beta union and sign-to-`H_tail` splice are closed.

The adjacent order-40/order-45 rescue `[80,80.5]` also passes production,
replay, validation, and its tail contract (408 strict rows). The local union
now contains 17 paired units and 4,125 rows in one component `[78.25,80.5]`,
with the remaining gap `[80.5,100]`.

The next adjacent rescue `[80.5,81]` also passed production, independent
replay, validation, and its order-40/order-45 tail contract (410 strict rows;
coefficient ratio `0.0082449214600909`, maximum weighted derivative ratio
`0.014515164435664`).  The executable local-union audit now reports 18 paired
units, 4,535 rows, one connected component `[78.25,81]`, and the remaining
gap `[81,100]`.  This is still candidate evidence only and does not alter G2
or G6.

The adjacent rescue `[81,81.5]` also passed production, independent replay,
validation, and its order-40/order-45 tail contract (413 strict rows;
coefficient ratio `0.0084588024485061`, maximum weighted derivative ratio
`0.01488704789104`).  The executable local-union audit now reports 19 paired
units, 4,948 rows, one connected component `[78.25,81.5]`, and the remaining
gap `[81.5,100]`.  This remains candidate evidence only and does not alter G2
or G6.

The next rescue `[81.5,82]` also passed production, independent replay,
validation, and its order-40/order-45 tail contract (417 strict rows;
coefficient ratio `0.0084186163032749`, maximum weighted derivative ratio
`0.014756913907960`).  The executable local-union audit now reports 20 paired
units, 5,365 rows, one connected component `[78.25,82]`, and the remaining gap
`[82,100]`.  This remains candidate evidence only and does not alter G2 or
G6.

The next rescue `[82,82.5]` also passed production, independent replay,
validation, and its order-40/order-45 tail contract (420 strict rows;
coefficient ratio `0.0086343918855855`, maximum weighted derivative ratio
`0.015130493650468`).  The executable local-union audit now reports 21 paired
units, 5,785 rows, one connected component `[78.25,82.5]`, and the remaining
gap `[82.5,100]`.  This remains candidate evidence only and does not alter G2
or G6.

The next rescue `[82.5,83]` also passed production, independent replay,
validation, and its order-40/order-45 tail contract (421 strict rows;
coefficient ratio `0.0085925848542152`, maximum weighted derivative ratio
`0.014997772599790`).  The executable local-union audit now reports 22 paired
units, 6,206 rows, one connected component `[78.25,83]`, and the remaining gap
`[83,100]`.  This remains candidate evidence only and does not alter G2 or
G6.

The next rescue `[83,83.5]` also passed production, independent replay,
validation, and its order-40/order-45 tail contract (424 strict rows;
coefficient ratio `0.0088102181453309`, maximum weighted derivative ratio
`0.01537298854737`).  The executable local-union audit now reports 23 paired
units, 6,630 rows, one connected component `[78.25,83.5]`, and the remaining
gap `[83.5,100]`.  This remains candidate evidence only and does not alter G2
or G6.

The next rescue `[83.5,84]` also passed production, independent replay,
validation, and its order-40/order-45 tail contract (427 strict rows;
coefficient ratio `0.0087667938560066`, maximum weighted derivative ratio
`0.015237716793860`).  The executable local-union audit now reports 24 paired
units, 7,057 rows, one connected component `[78.25,84]`, and the remaining gap
`[84,100]`.  This remains candidate evidence only and does not alter G2 or
G6.

The next rescue `[84,84.5]` also passed production, independent replay,
validation, and its order-40/order-45 tail contract (430 strict rows;
coefficient ratio `0.0089862484347707`, maximum weighted derivative ratio
`0.01561451035625`).  The executable local-union audit now reports 25 paired
units, 7,487 rows, one connected component `[78.25,84.5]`, and the remaining
gap `[84.5,100]`.  This remains candidate evidence only and does not alter G2
or G6.

The executable local-union audit
`scripts/audit_surface_scaled_bulk_cwin3p2_high_union.py` now confirms the
stronger coverage fact without overclaiming it: 25 paired high-order units,
7,487 rows, and two connected beta components `[78.25,84.5]` and
`[100,100.25]`. It reports the exact unresolved gap `[84.5,100]`; this is
the next finite-bridge production target.

The high-order tail dependency has now been audited separately by
`scripts/verify_surface_scaled_bulk_cwin3p2_high_tail_contract.py`: all 16
current production files with the CWIN=`3/2`, order-30/order-37 header satisfy
the coefficient and weighted derivative contraction for `q=0..30` and
`r=0..39`; the worst ratio is `0.0173228687`. This closes only the analytic
contraction sub-gate. It does not supply beta adjacency, moving-edge coverage,
replay manifests, or the sign-to-`H_tail` splice, so G2/G6 remain unchanged.

The adjacent rescue `[84.5,85]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (434 strict
rows; coefficient ratio `0.0089412111245136`, maximum weighted derivative ratio
`0.01547672428551`, worst case `(40,47)`). The executable local-union audit
reports 26 paired units and 7,921 rows, with connected components `[78.25,85]`
and `[100,100.25]`; the exact unresolved gap is now `[85,100]`. This remains
candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[85,85.5]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (437 strict
rows; coefficient ratio `0.0091624510377665`, maximum weighted derivative ratio
`0.015855038331194`, worst case `(40,47)`). The executable local-union audit
reports 27 paired units and 8,358 rows, with connected components
`[78.25,85.5]` and `[100,100.25]`; the exact unresolved gap is now
`[85.5,100]`. This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[85.5,86]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (438 strict
rows; coefficient ratio `0.0091158055213317`, maximum weighted derivative ratio
`0.015714774313677`, worst case `(40,47)`). The executable local-union audit
reports 28 paired units and 8,796 rows, with connected components
`[78.25,86]` and `[100,100.25]`; the exact unresolved gap is now `[86,100]`.
This remains candidate evidence only and does not alter G2 or G6.

On 2026-07-20 the next preregistered high-order CWIN=3/2 unit
`[101.75,101.8125]` failed at the moving-edge stress point under the
unchanged order-30/order-37, 180-bit contract.  The retained empty capture is
`scripts/surface_scaled_bulk_cwin3p2_high_101p75_101p8125.failed.txt`, and
the incident record is `docs/INCIDENT-SCALED-BULK-101P75-101P8125-20260720.md`.
The preceding unit `[101.6875,101.75]` did pass production and replay and is
manifested at
`run-manifests/surface-scaled-bulk-cwin3p2-high-101p6875-101p75-20260720.json`.
Neither record changes the candidate-only status of the scaled campaign or
promotes G2/G6; a transformed-coordinate or asymptotic replacement requires
its own preregistration and an independent sign-to-`(H_tail)` relay.

The preregistered delta-split diagnostic for the hybrid right-edge wedge also
failed to repair the five-family enclosure: both split bands remain positive
at `lambda=[2.70,2.72]` but negative at `[2.80,2.82]`.  The exact figures and
disposition are recorded in
`docs/INCIDENT-G2-RIGHT-EDGE-DELTA-SPLIT-20260720.md`.  This is a rejected
candidate route, not a theorem counterexample; the missing wedge still needs
a new sign-preserving analytic lemma.

The preregistered side-three central-chart diagnostic was also retired: its
finite geometry and recomputed tail gap still gave `P0_lower<0` at
`lambda=[2.80,2.82]`.  See
`docs/INCIDENT-G2-RIGHT-EDGE-SIDE3-20260720.md`.  This confirms that changing
the quadrature side/tail constants within this five-family architecture is
not a closure route.

## Provenance-validator portability repair (2026-07-20)

The four historical validators for the compact/left/right relay lanes now
pass in the current Windows checkout after their read-only `git show` calls
were given an explicit `safe.directory` configuration. This changes no
transcript, dependency hash, numerical bound, or gate state; it only prevents
Git's ownership guard from masking the existing provenance checks. The
rerun outputs are:

```text
bulk beta-Taylor:          90 beta boxes, 3222 t boxes
bulk beta-Taylor [15,20]:  89 beta boxes, 4736 t boxes
left edge:                 170 beta boxes, 170 normalized, 883 regular
right edge:                410 beta boxes, 410 normalized, 6448 regular
```

G3--G5 remain `CERTIFIED` on their stated scopes; this repair does not
promote G2, K2, K4, S1'''/S2''', or G6.

K4 positive-band continuation (2026-07-19): the preregistered isolated
campaign `[0.0305,0.05]` passed all 39 adjacent bands in production and fresh
replay, with 89,856 terminal cells and worst normalized fraction
`0.501618819006`.  The provenance manifest is
`run-manifests/surface-remainder-k4-positive-0305-0500-20260719.json`.
This is candidate local evidence only; the regular endpoint, `t`-union,
regular-ball overlap, and literal S1'''/S2''' judges remain open, so K4/G6 are
unchanged.

Finite-beta bridge topology audit (2026-07-20): requiring a paired replay for
every admitted transcript now gives one component `[20,101.625]`, with exact
remaining gap `[101.625,1000/9]`.  The historical unpaired run on
`[78.125,78.25]` remains intentionally excluded; the replacement
production/replay pair is admitted and manifested in
`run-manifests/surface-scaled-bulk-cwin3p2-high-78-seam-20260719.json`.
The successors `[100.25,100.3125]` and `[100.3125,100.5625]` subsequently
passed production, independent replay, and strict validation (303 rows and
1,220 rows respectively), with manifests
`run-manifests/surface-scaled-bulk-cwin3p2-high-100p25-20260719.json`; the
second manifest is
`run-manifests/surface-scaled-bulk-cwin3p2-high-100p3125-100p5625-20260719.json`.
The continuation `[100.8125,101.0625]` and the fresh continuation
`[101.0625,101.3125]` also passed production, independent replay, strict
validation, and exact adjacency; the latter is owned by
`run-manifests/surface-scaled-bulk-cwin3p2-high-101p0625-101p3125-20260719.json`.
The next continuation `[101.3125,101.5625]` also passed under the same
contract and is owned by
`run-manifests/surface-scaled-bulk-cwin3p2-high-101p3125-101p5625-20260719.json`.
The single-unit continuation `[101.5625,101.625]` then passed production,
independent replay, and strict validation (320 rows), and is owned by
`run-manifests/surface-scaled-bulk-cwin3p2-high-101p5625-101p625-20260720.json`.
The immediately following standard unit hit `min_dt` at `t=2.306947011918975`;
the failed transcript and isolated order-40/order-45 rescue timeout are
recorded in `docs/INCIDENT-SCALED-BULK-101P625-BOUNDARY-20260719.md` and
`docs/INCIDENT-SCALED-BULK-RESCUE-101P625-20260720.md`.
The short-ceiling timeout and excluded `1/32` retry are recorded in
`incidents/INC-SCALED-BULK-CWIN3P2-HIGH-100P25-TIMEOUT-20260719.md`.
See
`docs/SURFACE-FINITE-BETA-BRIDGE-COVERAGE-AUDIT-20260719.md` and
`scripts/audit_surface_finite_beta_bridge_candidate_coverage.py`; this is
topology only and does not promote G2.

The paired high-order union audit now counts 80 units and 29,441 strict rows
on the connected component `[78,101.625]`; this is an updated arithmetic
inventory only. The sign-to-`(H_tail)` implication remains unproved.

Read-only aggregate audit (2026-07-19): the archived regular and CWIN=3/2
candidate validators, together with the high-order seam validators, all pass
(36/36, including the separate 80-unit high-order union audit).  The driver is
`scripts/audit_surface_scaled_bulk_full_candidate_coverage.py`; it reruns each
child validator without changing manifests or gate status.  The reported
transcript total is 55,409 strict rows across the selected lanes; the isolated
high-order union itself is 80 paired units and 29,441 rows.  This is an
arithmetic inventory only: it does not identify a common (H_{\rm tail})
majorant, does not bridge the seam by theorem, and does not promote G2 or G6.

Continuation summary for the completed high-order CWIN=3/2 campaign:
`[98,98.5]`, `[97.5,98]`, `[98.5,99]`, `[99,99.5]`, and `[99.5,100]`
all passed production, independent replay, strict validation, and their
dedicated tail contracts. The final local union audit reports `56` paired
units and `22,208` rows with one component `[78.25,100.25]`. This summary is
candidate evidence only; it does not promote G2 or G6, and the manuscript's
analytic sign-to-`(H_tail)` splice remains open.

The adjacent CWIN=3/2 rescue `[99.5,100]` subsequently passed production,
independent replay, strict validation (`516` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0115635547535340`,
maximum weighted derivative ratio `0.01893823367660`, worst case `(40,47)`).
The local union now reports 56 paired units and 22,208 rows, with the single
component `[78.25,100.25]` after including the previously certified
`[100,100.25]` unit.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[99,99.5]` subsequently passed production,
independent replay, strict validation (`512` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0116319508842780`,
maximum weighted derivative ratio `0.01910944436915`, worst case `(40,47)`).
The local union now reports 55 paired units and 21,692 rows, with components
`[78.25,199/2]` and `[100,100.25]`; the exact gap remains `[199/2,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[98.5,99]` subsequently passed production,
independent replay, strict validation (`511` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0113892257624208`,
maximum weighted derivative ratio `0.01871510067577`, worst case `(40,47)`).
The local union now reports 54 paired units and 21,180 rows, with components
`[78.25,99]` and `[100,100.25]`; the exact gap remains `[99,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[98,98.5]` subsequently passed production,
independent replay, strict validation (`508` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0114561268689630`,
maximum weighted derivative ratio `0.018884326232608`, worst case `(40,47)`).
The local union now reports 52 paired units and 20,163 rows, with components
`[78.25,195/2]`, `[98,197/2]`, and `[100,100.25]`; exact gaps remain
`[195/2,98]` and `[197/2,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[90.5,91]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (466 strict
rows; coefficient ratio `0.0099904144468530`, maximum weighted derivative ratio
`0.016890028825740`, worst case `(40,47)`). The executable local-union audit
reports 38 paired units and 13,340 rows, with connected components
`[78.25,91]` and `[100,100.25]`; the exact unresolved gap is now `[91,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[90,90.5]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (463 strict
rows; coefficient ratio `0.0100450105884944`, maximum weighted derivative ratio
`0.017042139751099`, worst case `(40,47)`). The executable local-union audit
reports 37 paired units and 12,874 rows, with connected components
`[78.25,90.5]` and `[100,100.25]`; the exact unresolved gap is now `[90.5,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[89.5,90]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (461 strict
rows; coefficient ratio `0.0098153667363124`, maximum weighted derivative ratio
`0.016657031474575`, worst case `(40,47)`). The executable local-union audit
reports 36 paired units and 12,411 rows, with connected components
`[78.25,90]` and `[100,100.25]`; the exact unresolved gap is now `[90,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[89,89.5]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (459 strict
rows; coefficient ratio `0.0098683864009607`, maximum weighted derivative ratio
`0.01680684499407`, worst case `(40,47)`). The executable local-union audit
reports 35 paired units and 11,950 rows, with connected components
`[78.25,89.5]` and `[100,100.25]`; the exact unresolved gap is now `[89.5,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[88.5,89]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (457 strict
rows; coefficient ratio `0.0096403552243841`, maximum weighted derivative ratio
`0.01642299229284`, worst case `(40,47)`). The executable local-union audit
reports 34 paired units and 11,491 rows, with connected components
`[78.25,89]` and `[100,100.25]`; the exact unresolved gap is now `[89,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[88,88.5]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (453 strict
rows; coefficient ratio `0.0096917911363525`, maximum weighted derivative ratio
`0.01657047256498`, worst case `(40,47)`). The executable local-union audit
reports 33 paired units and 11,034 rows, with connected components
`[78.25,88.5]` and `[100,100.25]`; the exact unresolved gap is now `[88.5,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[87.5,88]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (451 strict
rows; coefficient ratio `0.0094654062148275`, maximum weighted derivative ratio
`0.01618792575972`, worst case `(40,47)`). The executable local-union audit
reports 32 paired units and 10,581 rows, with connected components
`[78.25,88]` and `[100,100.25]`; the exact unresolved gap is now `[88,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[87,87.5]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (448 strict
rows; coefficient ratio `0.0095152515371398`, maximum weighted derivative ratio
`0.016333036784259`, worst case `(40,47)`). The executable local-union audit
reports 31 paired units and 10,130 rows, with connected components
`[78.25,87.5]` and `[100,100.25]`; the exact unresolved gap is now
`[87.5,100]`. This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[86.5,87]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (445 strict
rows; coefficient ratio `0.0092905469270466`, maximum weighted derivative ratio
`0.01595184749483`, worst case `(40,47)`). The executable local-union audit
reports 30 paired units and 9,682 rows, with connected components
`[78.25,87]` and `[100,100.25]`; the exact unresolved gap is now `[87,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent rescue `[86,86.5]` has now passed production, independent replay,
exact validation, and its dedicated order-40/order-45 tail contract (441 strict
rows; coefficient ratio `0.0093387952871365`, maximum weighted derivative ratio
`0.016094553137155`, worst case `(40,47)`). The executable local-union audit
reports 29 paired units and 9,237 rows, with connected components
`[78.25,86.5]` and `[100,100.25]`; the exact unresolved gap is now
`[86.5,100]`. This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[91,91.5]` subsequently passed production,
independent replay, strict validation (`469` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0102216378720204`,
maximum weighted derivative ratio `0.01727634362558`, worst case `(40,47)`).
The local union now reports 39 paired units and 13,809 rows, with components
`[78.25,91.5]` and `[100,100.25]`; the exact gap remains `[91.5,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[91.5,92]` subsequently passed production,
independent replay, strict validation (`473` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0101654729430792`,
maximum weighted derivative ratio `0.017121970954636`, worst case `(40,47)`).
The local union now reports 40 paired units and 14,282 rows, with components
`[78.25,92]` and `[100,100.25]`; the exact gap remains `[92,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[92,92.5]` subsequently passed production,
independent replay, strict validation (`476` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0103982433148090`,
maximum weighted derivative ratio `0.01750944446447`, worst case `(40,47)`).
The local union now reports 41 paired units and 14,758 rows, with components
`[78.25,185/2]` and `[100,100.25]`; the exact gap remains `[185/2,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[92.5,93]` subsequently passed its authorized
rerun, independent replay, strict validation (`477` rows), and dedicated
order-40/order-45 tail contract (coefficient ratio `0.0103405176785309`,
maximum weighted derivative ratio `0.01735284550635`, worst case `(40,47)`).
The local union now reports 42 paired units and 15,235 rows, with components
`[78.25,93]` and `[100,100.25]`; the exact gap remains `[93,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[93,93.5]` subsequently passed production,
independent replay, strict validation (`481` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0105748028454890`,
maximum weighted derivative ratio `0.017741431121993`, worst case `(40,47)`).
The local union now reports 43 paired units and 15,716 rows, with components
`[78.25,187/2]` and `[100,100.25]`; the exact gap remains `[187/2,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[93.5,94]` subsequently passed production,
independent replay, strict validation (`484` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0105155249493067`,
maximum weighted derivative ratio `0.017582641114288`, worst case `(40,47)`).
The local union now reports 44 paired units and 16,200 rows, with components
`[78.25,94]` and `[100,100.25]`; the exact gap remains `[94,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[94,94.5]` subsequently passed production,
independent replay, strict validation (`487` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0107512932336985`,
maximum weighted derivative ratio `0.01797229341174`, worst case `(40,47)`).
The local union now reports 45 paired units and 16,687 rows, with components
`[78.25,189/2]` and `[100,100.25]`; the exact gap remains `[189/2,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[94.5,95]` subsequently passed production,
independent replay, strict validation (`489` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0106904718706246`,
maximum weighted derivative ratio `0.017811347353818`, worst case `(40,47)`).
The local union now reports 46 paired units and 17,176 rows, with components
`[78.25,95]` and `[100,100.25]`; the exact gap remains `[95,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[95,95.5]` subsequently passed production,
independent replay, strict validation (`490` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0109276920662413`,
maximum weighted derivative ratio `0.01820202206083`, worst case `(40,47)`).
The local union now reports 47 paired units and 17,666 rows, with components
`[78.25,191/2]` and `[100,100.25]`; the exact gap remains `[191/2,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[95.5,96]` subsequently passed production,
independent replay, strict validation (`494` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0108653363538582`,
maximum weighted derivative ratio `0.018038954697954`, worst case `(40,47)`).
The local union now reports 48 paired units and 18,160 rows, with components
`[78.25,96]` and `[100,100.25]`; the exact gap remains `[96,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[96,96.5]` subsequently passed production,
independent replay, strict validation (`496` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0111039777237519`,
maximum weighted derivative ratio `0.018430608666128`, worst case `(40,47)`).
The local union now reports 49 paired units and 18,656 rows, with components
`[78.25,193/2]` and `[100,100.25]`; the exact gap remains `[193/2,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[96.5,97]` subsequently passed production,
independent replay, strict validation (`499` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0110400970840559`,
maximum weighted derivative ratio `0.018265454474974`, worst case `(40,47)`).
The local union now reports 50 paired units and 19,155 rows, with components
`[78.25,97]` and `[100,100.25]`; the exact gap remains `[97,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[97,97.5]` subsequently passed production,
independent replay, strict validation (`500` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0112801293578758`,
maximum weighted derivative ratio `0.01865804565246`, worst case `(40,47)`).
The local union now reports 51 paired units and 19,655 rows, with components
`[78.25,97.5]` and `[100,100.25]`; the exact gap remains `[97.5,100]`.
This remains candidate evidence only and does not alter G2 or G6.

The adjacent CWIN=3/2 rescue `[97.5,98]` subsequently passed production,
independent replay, strict validation (`506` rows), and its dedicated
order-40/order-45 tail contract (coefficient ratio `0.0112147334979443`,
maximum weighted derivative ratio `0.01849083882790`, worst case `(40,47)`).
The local union now reports 53 paired units and 20,669 rows, with components
`[78.25,197/2]` and `[100,100.25]`; the exact gap remains `[197/2,100]`.
This remains candidate evidence only and does not alter G2 or G6.

## Frontier continuation audit (2026-07-20)

Two preregistered standard-contract units were subsequently completed at the
finite-beta frontier:

```text
[101.75,101.78125]   321 t rows, production/replay exact, validator PASS
[101.78125,101.8125] 324 t rows, production/replay exact, validator PASS
```

Their paired manifests are
`surface-scaled-bulk-cwin3p2-high-101p75-101p78125-20260720.json` and
`surface-scaled-bulk-cwin3p2-high-101p78125-101p8125-20260720.json`.
The read-only topology audit now reports one paired component
`[20,1629/16]` and the exact remaining gap
`[1629/16,1000/9]`; the old unpaired overlap at `[625/8,313/4]` remains
excluded.  The next preregistered unit `[101.8125,101.84375]` reaches the
frozen `min_dt` boundary at `t≈3.1265558006` and is retired in
`INCIDENT-SCALED-BULK-101P8125-BOUNDARY-20260720.md`.

An isolated high-grid ratio diagnostic on the corresponding right-edge seam
also timed out before producing a row.  These results improve the candidate
inventory only; they do not change the G2 state, prove `(H_tail)`, or alter
K4/S1'''/S2'''/G6.

## Gap timeout recorded 2026-07-22

The first current uncovered beta interval, `[765/16,193/4]`, was retried
with the registered CWIN=`3/2` high-order backend (180-bit Arb, orders
30/37, cached Bessel values).  The process exceeded the 120-second execution
ceiling before emitting a terminal row.  No output or manifest was admitted;
the incident is recorded in
[`INCIDENT-G2-SCALED-BULK-GAP-765-16-20260722.md`](INCIDENT-G2-SCALED-BULK-GAP-765-16-20260722.md).
This is a design timeout, not a sign result, and the finite-beta relay remains
unproved.

The amended quarter-width cover then completed units 0--31, namely
`[193/4,225/4]`, with 4,866 strict-negative rows and exact
production/replay agreement.  These thirty-two units are archived in the
quarantined partial manifest
`surface-scaled-bulk-cwin3p2-mid-cover-partial-20260722.json`.
The fixed 83-unit cover still has 51 units outstanding, so this does not
change G2.

Unit 32, `[225/4,113/2]`, was then run under the unchanged contract and
failed at the registered minimum `t` width near `t=3.1113119102511955`.
No transcript or manifest was admitted for that unit; the incident is
recorded in `docs/INCIDENT-G2-MID-COVER-UNIT32-FAIL-20260722.md`.
The failure blocks continuation until an explicitly preregistered repair is
audited, and does not change the quarantined status of the first 32 units.

## Signed-bilinear endpoint candidate (2026-07-22)

An isolated endpoint experiment now forms the K2 bilinear cellwise before
summation, adds the registered outer-derivative charges, and charges the
order-five Bessel companion error explicitly.  The frozen grid-48 run passes
all 158 born `t` boxes on `[0,1/1000]`, with exact production/replay byte
equality and worst printed lower margin `0.884364280881655...`.  The transcript,
independent parser, and quarantine manifest are
`surface_signed_bilinear_endpoint_candidate_048.txt`,
`validate_surface_remainder_signed_bilinear_endpoint_candidate.py`, and
`surface-remainder-signed-bilinear-endpoint-candidate-20260722.json`.
This is a candidate cancellation witness only: it does not promote K2, G2,
G6, or the literal S1'''/S2''' union.
