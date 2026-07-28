# Surface finite-beta bridge — preregistration

**State:** `LEFT_PRODUCTION_AND_TAIL_AUDITED`; scaled bulk still open  
**Registered:** 2026-07-15, before the first scaled box result

## Objective

Replace the still-open positive-delta births of `(H_tail)` by an exact splice:

1. direct finite-beta certificates on
   `20 <= beta <= 1000/9`;
2. the already certified regular lane `0 <= delta <= 9/1000`, equivalently
   `beta >= 1000/9`;
3. the independent five-family right-edge cover on the moving wedge.

The splice point is the exact rational `beta = 1000/9`.  No decimal endpoint
is admissible.

## Exact scaling identity

Put `J_m(beta)=exp(-beta) I_m(beta)`.  If `a_m,b_m` are the two coefficient
families of the surface Wronskian, define the same expressions with every
`I` replaced by `J`.  Homogeneity gives

```text
A_m = exp(-4 beta) a_m,
B_m = exp(-4 beta) b_m,
W_scaled = exp(-8 beta) W.
```

Therefore `W_scaled<0` is exactly equivalent to `W<0`.  This is not an
asymptotic approximation.  It removes the common exponential magnitude before
Arb interval formation.

The beta jets are generated from the exact recurrence

```text
d^q I_n / d beta^q
  = 2^-q sum_{j=0}^q binom(q,j) I_{n-q+2j}
```

and the product with the Taylor series of `exp(-h)`.  Numerical
differentiation is forbidden.

The derivative tail uses the exact operator

```text
J_n' = (J_{n-1}+J_{n+1})/2 - J_n.
```

The recurrence `I_{n-1}/I_n=I_{n+1}/I_n+2n/beta` gives
`|J_n^(q)| <= [2(1+2n/beta)]^q J_n`.  Since each surface coefficient
is a positive sum of degree-four monomials in adjacent `J` values, Leibniz
gives the executable majorant

```text
|C_m^(q)| <= [8(1+2(m+1)/beta_lo)]^q C_m.
```

The factor `8` is mandatory.  Reusing the unscaled coefficient factor `4`
would omit the `exp(-beta)` derivative contribution.

## Judges fixed before results

1. **Identity overlap.**  At `beta=20`, modes `1,...,8` and derivative orders
   `0,...,4`, the scaled coefficient jets must overlap the independent
   product-rule transform of the unscaled jets.
2. **First bulk box.**  `[20,201/10]` must close on the existing beta/t Taylor
   orders `(12,9)` without a beta step below `1/100`.
3. **First left box.**  The same beta box must close both the normalized
   `t in (0,1/5]` row and the ordinary `t in [1/5,3/5]` row.
4. **Stress ladder.**  Only after judges 1--3 pass, probe the exact boxes
   `[25,251/10]`, `[40,401/10]`, `[80,801/10]`, and
   `[111,1000/9]`.  A failure records the smallest beta step reached and the
   first unresolved `t` location.
5. **Tail contract.**  **Audited.** The registered
   factor-8 derivative majorant is exercised by
   `scripts/surface_finite_beta_scaled_tail_oracle.py` for both coefficient
   families and beta derivative orders `0..4` on the high-beta stress tail;
   every direct 12-term partial sum lies strictly below the majorant.  The
   written infinite-tail derivation in
   `SURFACE-FINITE-BETA-BRIDGE-TAIL-CONTRACT.md` and the executable
   `scripts/verify_surface_scaled_tail_contract.py` now audit the decreasing
   coefficient ratios, the factor-8 derivative bound, and the geometric
   remainder on the four stress bands used by the production partition.
   The scaled-left union is now terminal: all 92 grouped units pass the
   coverage validator (912 beta intervals, 4,636 strict rows), and the fresh
   independent grouped replay reproduces every row.  This promotion applies
   only to the left-edge lane; the scaled bulk union remains open, and the
   beta-20--25 right-edge endpoint is separately rejected in
   `INC-G5-BETA20-25-ENDPOINT.md`.
6. **Coverage.**  Production must list every rational beta interval exactly
   once, prove adjacency from `20` to `1000/9`, include hashes and versions,
   and be checked by a separate validator.  Bulk and left-edge unions are
   independent certificate families.
7. **Splices.**  The bulk/left boundary is the closed rational `t=3/5`.
   The regular/G5 moving boundary must have a closed overlap on every terminal
   beta interval.  Open-set coverage or sampled overlap is rejected.

## Step-design ladder

The width `1/10` stress boxes test feasibility, not the final production
cost.  Before observing the `beta=40` result, the allowed beta-width ladder
is fixed as

```text
1/10, 1/5, 1/2, 1, 2.
```

For each of the bands `[20,25]`, `[25,40]`, `[40,80]`, and
`[80,1000/9]`, a separate design sweep tries these widths in increasing
order and records the last width whose complete band cover passes.  Production
uses a frozen rational partition at or below that last green width; it may not
change width in response to an individual production row.  The final short
box is the exact rational remainder to the band endpoint.  Failure of a wider
candidate never invalidates an already green narrower candidate.

## Falsification and fallback

If the scaled finite-beta Taylor architecture loses resolution before
`1000/9`, the last certified rational beta becomes a registered intermediate
splice.  The remaining interval returns to the analytic positive-delta lane;
no certified claim is inferred past the last green box.  Increasing precision
alone is not a remedy for a non-contracting Taylor remainder.

The Poisson integral remainder for individual scaled Bessel factors is already
banked in `surface_bessel_integral_remainder.py`.  It does not by itself bound
the spatially integrated bilinear carrier: any fallback must preserve the
determinant cancellation before absolute values are taken.

## Left-splice design amendment after the first stress failure

The first box at `beta=20` passed with splice `1/5`.  At
`[40,401/10]`, the normalized row failed near
`t=0.1993484497...` even after the beta width was repeatedly halved below
`10^-6`.  This rejects beta refinement as a cure and localizes the loss to
the zero-centred `t` Taylor radius.  No certificate was produced by that run.

Before the next result, the replacement splice is fixed at the exact rational
`19/100`.  The normalized judge must cover `(0,19/100]` and the ordinary
judge `[19/100,3/5]` on the same beta box.  If this fails, the route is not
allowed to move the splice again without a new recorded amendment and a fresh
ordinary-overlap probe.

## High-beta left-edge paired-moment amendment

With the frozen splice `19/100`, the generic normalized evaluator failed on
the preregistered high anchors near `t=0.1288427353` for `[80,801/10]` and
near `t=0.1048252869` for `[111,1000/9]`.  No certificate was emitted, and
beta narrowing is not used as a response.

Before the replacement result, write the non-alternating endpoint moments as
`S_X,r=sum m^r c_X,m`.  For `k>=1`, the exact coefficient of `t^(2k-2)` in
`W(t)/t^3` is fixed as

```text
2 (-1)^k sum_{0<=p<q, p+q=k}
  [1/((2p)!(2q+1)!)-1/((2p+1)!(2q)!)]
  (S_A,2p+1 S_B,2q+1 - S_A,2q+1 S_B,2p+1).
```

The design retains the nine coefficients through `t^16`, beta order 20,
the exact parity zero at Wronskian order 20, and an absolute derivative-21
remainder.  Every coefficient and beta derivative must overlap the generic
value `W^(2k+1)(0)/(2k+1)!`.  The replacement is tested first on
`[80,801/10]`, then `[111,1000/9]`, with the unchanged beta widths and
splice `19/100`; the ordinary lane remains `[19/100,3/5]`.  Any failure blocks
this paired left route, and no order, splice, precision, or grid fallback is
pre-authorized.

Both high anchors passed the paired evaluator: `[80,801/10]` used 2
normalized and 4 regular boxes; `[111,1000/9]` used 4 normalized and 6 regular
boxes.  Before selecting one uniform production backend, the same frozen
paired evaluator must also pass `[20,201/10]` and `[40,401/10]`.  These are
overlap checks with the already green generic low-beta lane; failure would
force an explicit low/high production splice rather than invalidate either
existing high-anchor result.

## Bulk-cache design amendment

The unmodified scaled bulk probe at `[40,401/10]` was terminated without a
result after more than twenty wall minutes.  Inspection found that every
candidate `t` box recomputed the identical `sin(mT),cos(mT)` balls separately
for both families, every beta derivative, and every t derivative.  This is an
implementation repetition, not a mathematical obstruction.

Before the replacement result, the cached evaluator is fixed: for each mode
and t-derivative order it forms the weighted trigonometric ball once and reuses
it in all beta/family sums.  The Taylor polynomial, derivative-tail majorants,
remainder charges, precision, and subdivision rules are unchanged.  Promotion
requires an executable overlap between cached and original scaled evaluations
on `[20,201/10]` before the `[40,401/10]` stress box is retried.

The first cached stress retry was itself terminated without a result after
several minutes: it still formed one sine/cosine pair per t-derivative order.
Before the next retry the cache is strengthened, without changing a bound, to
form exactly one pair per mode; derivative orders use the exact four-cycle
`sin, cos, -sin, -cos` and multiply by `m^r`.  The same overlap regression is
mandatory again.

The second cached retry was likewise terminated without a result after
several minutes.  A third exact repetition was then isolated: the 286
geometric Fourier-tail majorants depend on the beta box, family, beta
derivative and t derivative, but not on the t-box midpoint.  The next retry
caches each such majorant once per beta box.  Its formula and outward ball are
unchanged, and the original/cached overlap regression remains mandatory.

## Fixed finite rectangle amendment

The completed `[40,401/10]` stress box with the original moving cutoff passed
only after beta bisection to `1/20`; it required 5,639 terminal t boxes.  A
`Cwin=4` design reduced this to 1,967 boxes but failed its preregistered cost
judge of fewer than 1,000.  Extending G5 merely moves the degenerating bulk
boundary and is therefore retired as the preferred finite bridge.

Before any fixed-strip result, the finite domain is repartitioned exactly as

```text
(0,3/5]                 scaled left quotient/ordinary splice,
[3/5, pi-1/10]          scaled fixed bulk,
[pi-1/10, pi)           scaled right quotient/ordinary splice.
```

The right endpoint quotient uses splice `d=1/4000`; the ordinary right lane
covers `[1/4000,1/10]`.  The bulk implementation uses the strict rational
upper bound `PI_UP-1/10`, hence overlaps the true right lane.  The first judge
is `[40,401/10]`: both fixed bulk and fixed right must pass at beta width
`1/10`, and the bulk must use fewer than 1,000 t boxes.  No G5 extension is
needed or inferred from this amendment.

## Fixed finite rectangle first result

The fixed bulk probe on `[40,401/10]` passed the sign judge at beta width
`1/10`, but used 1,963 terminal `t` boxes.  It therefore **failed** the
pre-registered cost judge and carries no production or theorem load.  The
fixed right strip is tested unchanged before any replacement bulk design is
selected, so an endpoint failure cannot be hidden by retuning the interior.

That unchanged fixed-right probe failed in its normalized lane near
`d=1.953125e-6`; no certificate was emitted.  Thus the complete fixed-strip
judge failed independently of the bulk cost judge.

Before the next probes, the recovery order is frozen as follows.  For the
bulk, retain beta width `1/10` and try `t_order=11`, then `t_order=13`, stopping
at the first order that passes with fewer than 1,000 terminal boxes; changing
Taylor order changes no domain or sign target.  For the right strip, first
repeat only `[40,4001/100]` at beta width `1/100` with the same `d_order=9`
and endpoint splice.  A green diagnostic would localize the failure to the
beta-remainder width but would still carry no production load.  A failure at
that width rejects this fixed-right evaluator pending a sharper endpoint
beta remainder; the endpoint or splice may not be moved in response.

The width-`1/100` right diagnostic failed at the same reported location,
`d=1.953125e-6`.  Under the frozen ladder this rejects the present
fixed-right evaluator.  In particular, no further beta narrowing, precision
increase, or endpoint-splice movement is licensed as a response; a replacement
must sharpen the endpoint determinant cancellation itself and receive its own
contract and overlap tests before any result is read.

The first bulk recovery candidate, `t_order=11`, passed on
`[40,401/10] x [3/5,PI_UP-1/10]` at the unchanged beta width `1/10` with 547
terminal `t` boxes.  This passes the frozen cost judge, so the `t_order=13`
candidate is not tried.  The result fixes the preferred production order for
the scaled fixed bulk, but it remains design evidence until an exhaustive
finite-beta union, provenance-bearing transcripts, and a union validator are
implemented.

## Endpoint determinant-jet replacement

Before any replacement right-edge result, the endpoint lane is fixed to retain
the beta derivatives of the signed endpoint determinant through order 20.
Writing

```text
S_X,r = sum_{m>=1} (-1)^(m+1) m^r c_X,m,
```

the exact endpoint value is

```text
W(pi-d,beta)/d^3 |_(d=0)
  = (2/3) (S_A,3 S_B,1 - S_A,1 S_B,3).
```

The implementation must check this formula against `-W'''(pi)/6` for every
retained beta derivative.  It keeps the existing `d` expansion through order
9, but delays the first absolute beta remainder from derivative 13 to
derivative 21.  The ordinary lane remains at beta order 12.  The frozen
falsification ladder is beta order 20, then 24 only if order 20 fails, on the
original stress box `[40,401/10]` of width `1/10`; stop at the first green
candidate.  Neither `d=1/4000`, `d=1/10`, nor the beta width may move.

Both endpoint beta orders 20 and 24 failed at the identical reported
microbox beginning at `d=1.953125e-6`.  A direct Arb diagnostic at order 20
enclosed the endpoint value as `[-2e-41 +/- 4.83e-42]`, while the generic
mixed-derivative enclosure first lost sign in the third microbox.  This
rejects beta-order escalation and localizes the dependency loss to the
unsimplified positive powers of `d`.

Before the next result, the replacement is therefore fixed algebraically.
Pair the endpoint moment terms before interval evaluation.  For `k>=1`, the
coefficient of `d^(2k-2)` in `W(pi-d)/d^3` is evaluated as

```text
2 (-1)^(k+1) sum_{0<=p<q, p+q=k}
  [1/((2p)!(2q+1)!)-1/((2p+1)!(2q)!)]
  (S_A,2p+1 S_B,2q+1 - S_A,2q+1 S_B,2p+1).
```

This is an identity, not a numerical rearrangement.  Terms through `k=5`
(`d^8`) are retained with beta order 20; the same absolute beta and spatial
derivative majorants enclose the two Lagrange remainders.  Every retained
coefficient must overlap the generic value `-W^(2k+1)(pi)/(2k+1)!` in an
executable regression.  The stress domain, beta width, endpoint splice and
right-strip width remain unchanged.  Failure rejects this paired-moment lane;
no further order or grid tuning is pre-authorized.

The paired-moment lane passed its algebraic overlap checks and moved the first
loss from `d=1.953125e-6` to `d=4.1015625e-5`, but still failed the frozen
stress judge.  At the beta midpoint its five retained paired coefficients were
all strict negative intervals; the loss appeared only after evaluating all
their beta Taylor polynomials in one natural interval.  Thus the paired lane
is rejected as an evaluator, while its exact coefficient identities remain
available as lemmas.

Before the next result, a sign-separated endpoint judge is fixed.  Each of the
five paired coefficients (`d^0,d^2,...,d^8`) receives its own beta-Taylor
enclosure of order 20 and its own absolute derivative-21 remainder, using
moment powers through 13 at `beta_hi`.  All five must be strictly negative on
the full beta box.  The four `d`-positive correction terms are then discarded
only in the upper-bound direction; the certified endpoint coefficient plus
the unchanged order-12 spatial Lagrange error must remain strictly negative.
This proves the whole normalized `d` interval without evaluating correlated
powers in one interval.  The original `[40,401/10]`, width `1/10`, splice
`1/4000`, and `d_max=1/10` remain frozen.  Any non-negative coefficient or
failed final margin rejects this judge with no fallback tuning authorized.

The sign-separated coefficient checks passed, but their order-12 spatial
Lagrange charge still lost the final margin at the same
`d=4.1015625e-5`.  This rejects that remainder judge.  Before a replacement
result, one exact parity identity is added: both sine series are odd in
`d=pi-t`, their `t` derivatives are even, and hence `W(pi-d)` is odd.  Its
order-12 endpoint coefficient is therefore identically zero.  The parity-aware
Taylor formula retains the same five paired coefficients through `d^8` after
division by `d^3`, inserts the exact zero at Wronskian order 12, and charges
derivative 13, i.e. a `d^10` normalized remainder.  Beta order 20, coefficient
sign judges, the full stress box, and every rational boundary remain unchanged.
Failure of this parity-aware remainder rejects the normalized fixed strip.

The parity-aware derivative-13 remainder moved the first loss to
`d=0.0001083984375` but did not cover the complete normalized interval, so
that five-coefficient judge is rejected.  Before the next result, the same
identity is extended in one fixed step through Wronskian order 19: nine paired
coefficients (`d^0` through `d^16`) must each be strictly negative, order 20
is the exact parity zero, and derivative 21 supplies a normalized `d^18`
remainder.  This endpoint order is fixed before its signs are read; beta order,
stress domain, widths, and all rational splices remain unchanged.  Failure of
any of the nine sign rows or of the final derivative-21 margin rejects the
paired-coefficient route.

All nine sign rows and the parity-aware normalized lane passed on the original
`[0,1/4000]`.  The run then failed exactly at the first ordinary microbox,
`d=1/4000`; no complete right-strip certificate was emitted.  This separates
endpoint closure from the ordinary evaluator's small-`d` dependency loss.

Before the replacement result, the sole splice change is fixed at `d=1/500`,
the value already used by the audited compact right-edge lane.  The unchanged
nine-coefficient normalized judge must cover `[0,1/500]`, and the unchanged
order-12 ordinary judge must cover `[1/500,1/10]`, on the original beta stress
box of width `1/10`.  No further splice movement is authorized.  Both rows
must pass for a fixed-right design result.

The normalized judge covered `[0,1/500]` in one terminal box, but the ordinary
judge again failed exactly at its first point, `d=1/500`.  This rejects the
mixed normalized/ordinary right strip.  Before the next result, the ordinary
evaluator is removed from the fixed finite bridge and the unchanged
nine-coefficient parity judge is assigned the single full interval
`[0,1/10]`.  It must pass without subdivision or parameter changes on
`[40,401/10]`; failure rejects the fixed-right route.  This is a stronger
single-domain falsification, not an extrapolation from the green short row.

The initial full normalized box was non-negative and the adaptive diagnostic
ultimately failed near `d=0.0058929443`; the implementation did subdivide, so
it did not satisfy the stronger one-box wording, but the initial rejection
already falsifies that one-box judge.  The fixed-right route is retired and
carries no theorem load.

## Return to the moving bulk--G5 union

The fixed-strip experiment was a cost optimization, not a logical necessity.
The original exact partition remains

```text
[3/5, pi-3/(2 beta)]      scaled moving bulk,
[pi-3/(2 beta), pi)       finite/half-line G5 union.
```

Its scaled moving bulk already passed the `[40,401/10]` stress interval at
Taylor order 9, albeit with 5,639 terminal boxes after beta bisection.  Before
the replacement result, order 11 is fixed with the original `CWIN=3/2`, beta
width `1/10`, and unchanged domain.  The design judge is strict sign closure
with fewer than 2,500 terminal boxes on `[40,401/10]`; no order-13 retry is
pre-authorized.  Promotion still requires the exhaustive `[20,1000/9]` union,
the independently reproduced finite G5 unions, production provenance, and
executable seam validators.

Order 11 passed the frozen moving-bulk stress box `[40,401/10]` with 646
terminal `t` boxes, against 5,639 for the earlier order-9 route, and therefore
passes the 2,500-box design judge.  Before an exhaustive union is fabricated,
the unchanged order-11 evaluator is frozen on the three rational anchors
`[20,201/10]`, `[80,801/10]`, and `[111,1000/9]`.  Each must close without
beta bisection and with fewer than 2,500 terminal `t` boxes.  Failure of an
anchor blocks production partitioning; success licenses width-`1/10`
production units only, not a theorem claim.

The first launches of the beta-80 and beta-111 bulk anchors were terminated
without a result after an audit found that the wrapper called the adaptive
`bulk.cover` routine, which is allowed to bisect beta and therefore did not
implement the stated single-box judge.  Before either result is read, the
wrapper is replaced by a literal one-box `BetaTaylorBox` plus an exact moving
`t` cover.  It aborts as soon as a 2,500th terminal box would be accepted and
never changes the beta interval.  The already completed beta-20 and beta-40
outputs each printed one beta box, so they remain valid design probes; the two
high anchors are rerun under the corrected executable judge.

Under the corrected judge, `[80,801/10]` failed near
`t=2.2296076674` and `[111,1000/9]` failed near `t=1.9101249439`; neither
box was bisected.  This rejects direct moving-bulk production to the analytic
splice.  Before any localization result, test the exact boxes
`[60,601/10]` and `[70,701/10]` with the same one-box/cost judge.  If beta 60
fails, the next registered point is beta 50; if beta 70 passes, the next is
beta 75.  No other adaptive search is licensed.  These probes locate a clean
overlap target for the separately preregistered regular-K2 delta extension;
they do not weaken the existing green beta-40 result.

## Registered localization result (2026-07-16)

The authorized follow-up was executed in the required order. The one-box
order-11 moving-bulk judge failed at beta `60--60.1`, first losing sign near
`t=2.5470737520174302`. The preregistered fallback beta `50--50.1` was then
run and failed near `t=2.7584514361433383`. Both failures occurred without
beta bisection and with the fixed `CWIN=3/2` domain. Consequently the
scaled moving-bulk route is not licensed for production beyond the already
green beta-40 design box; no additional beta search or theorem load is
claimed here.
