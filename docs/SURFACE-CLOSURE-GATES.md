# Surface Theorem closure gates

**Status date:** 2026-07-16
**Submission state:** `DO_NOT_SUBMIT`

This board separates maintenance, local analytic hypotheses, global relay coverage,
and the final editorial seal. Passing one row never promotes another row implicitly.
The authoritative mathematical statement remains
`papers/surface-complete/surface_theorem_complete.tex`.
The current remainder-localization constants and failure rules are pre-registered in
[`SURFACE-REMAINDER-PREREG.md`](SURFACE-REMAINDER-PREREG.md).
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

| Gate | Scope | Current state | Terminal evidence required |
|---|---|---|---|
| G0 | v88 numerical sanitation, T1--T7 | `PASS` | five independently rerun authoritative outputs, six nonempty run manifests including T1, reciprocal supersession, and green executable audit |
| G1 | optional local mirror refinement `(H_cube)` | `REMOVED_FROM_TERMINAL_PAPER` | the preceding manuscript step already proves the mirror bound `M` unconditionally and the optional `M_sharp` subsection explicitly carried no relay load.  A static audit now requires `H_cube`, `M_sharp`, and the conditional subsection to be absent while retaining unconditional `M` and its corollary.  K4 remains a documented research lane but is not a theorem or submission gate |
| G2 | analytic bulk tail `(H_tail)` | `REGULAR_008_AND_HYBRID_009_CERTIFIED` | the regular lane independently derives exact `T`, `r2`, `r3`, `r4`, `r5`, and `r6`; eight manifested production segments close `[0,1/125] x [0,pi]` on all 158 born `t` boxes using four incremental core boxes, eight annulus births, physical split `1181/1000`, band radius `66/5`, a frozen mixed `384/192/384` grid map, and worst strict lower margin `0.0000111964` at index 50, absorbing positive births 1--7; the next hybrid birth `[1/125,9/1000]` passes its complete 158-unit union validator from frozen source commit `982959ea`, with worst strict lower margin `0.0169551281` at `parent_145` and the moving-edge complement assigned to G5.  The exact finite-beta bridge is preregistered as an alternative to all 42 later delta births: scaled direct certificates would cover `20<=beta<=1000/9`, then splice exactly to the current regular lane.  It has no theorem load until its scaled-tail contract and exhaustive unions pass |
| G3 | compact relay `[6,20]` | `CERTIFIED` | two bivariate beta/t Taylor Arb covers: 179 contiguous beta boxes, 7,958 strict t boxes, transcripts + manifests + executable coverage validators |
| G4 | left edge `t in (0,0.6]` | `SCALED_FINITE_INDEPENDENTLY_REPRODUCED` | `[3,20]` is closed by the manifested `W/t^3` + ordinary Taylor splice.  For `20<=beta<=1000/9`, the exact scaled paired-moment bridge through `t^16` uses the fixed `19/100` splice: 912/912 atomic production intervals and 4,636 rows pass the coverage/sign validator, and a fresh 16-worker replay reproduces all 912 intervals and 4,636 rows exactly after parsing.  The production and replay transcripts carry the same frozen head and dependency hashes.  This closes the scaled finite-beta evidence; it does not by itself remove the remaining G6 slots. |
| G5 | moving right edge | `FINITE_COVERS_INDEPENDENTLY_REPRODUCED` | the manifested compact union closes `3<=beta<=20`.  The relocated-splice design continues to beta 25.  The lower finite bridge has authoritative production plus fresh independent replay: 225/225 rows on `25<=beta<=30`, exact row equality, worst `H` lower `0.0199195495...` at `(2,74)`.  The upper finite bridge now also has production plus fresh independent replay: 375/375 rows on `30<=beta<=125`, exact row equality, worst `H` lower `0.0258956127...` at `(3,74)`.  For `beta>=125`, exact divided differences reduce the target to five scaled families with `H=P0/(4 B0^2)`: all 600 frozen design cells and all 600 production cells from source commit `1da7e414` pass, and the union validator gives worst `H` lower `0.0538267940...` at `(0,74)`.  The independent rerun reproduces all 600 rows byte-for-byte after JSON parsing from that same commit.  The order-only validator incident is documented without changing transcripts.  The compact-extension relay and its final theorem load remain open. |
| G6 | global theorem and paper seal | `BLOCKED` | G0--G5 terminal, all manuscript `[SLOT]` markers removed by proved/certified text, full build, citation audit, and independent claim audit |

The unscaled compact G4 engine is not a viable half-line substitute.  A post-certificate
extension attempt on the first box `[20,20.1]` consumed more than 15 CPU
minutes without completing, versus seconds per box lower down, and was
terminated without a result.  No claim or transcript was produced.  That
negative result applies to direct use of exponentially large `I_m(beta)`.
The newly preregistered finite bridge instead uses the exact common scaling
`J_m=exp(-beta)I_m`, under which `W_scaled=exp(-8 beta)W`; it is a distinct
architecture and remains design-only until its pre-registered probes run.

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
