# Step 8b.24 S1a–S4 — static semantic audit

Status: **STATIC ONLY — NOT COMPILER-VERIFIED**.

Scope: bricks 23–29 in `STEP8B24_BRICK_SCHEDULE`.

## Gate S1 — generated inverse pair at independent source scales

**PASS (static).**

The ambient precision and Green fix the RG ratio to `L` and the independent
coarse carrier to `2*(K*Q)`. Both ordered inverse laws are transported through
the sealed source-separated full-site equivalence. No diagonal `K=L` cast or
free inverse data appears.

Their complexifications are canonical and inherit both inverse laws from the
real pair; a complex inverse is not supplied independently.

## Gate S2 — exact Step-7b carrier and precision dictionary

**PASS (static).**

- The carrier exposes the source factorization
  `fine side = L^(depth+1)`, `coarse side = 2*(K*Q)`.
- The active-site equivalence is constructed from the generated one-block
  coordinate map and the full-site source equivalence.
- Real ambient fields are pulled back internally and their zero extension is
  identified with coordinate transport followed by literal fibre
  complexification.
- The Step-7b precision is the literal full-box precision transported along
  that equivalence.
- Equality with the canonical complexified generated precision is first
  proved on real fields from the source dictionary, then extended to every
  complex field using real/imaginary decomposition and complex linearity.

No operator equality is an input to the public endpoint.

## Gate S3 — physical Green identification by inverse uniqueness

**PASS (static).**

The transported generated Green is proved a left inverse of the literal
Step-7b full-box precision. The noncentral fine-symbol theorem handles the
zero and nonzero coarse modes separately, and the central stabilized
denominator is proved nonzero from positivity of the generated coefficient.
Inverse uniqueness then identifies the literal stabilized field with the
generated Green applied to the literal coefficient-one `Q'^*`.

The generic noncentral theorem is moved to a neutral owner without changing
its theorem/proof block. This removes a false dependency on the old diagonal
endpoint; it does not create a new mathematical producer.

## Gate S4 — exact finite Fourier endpoint

**PASS (static).**

The identified generated endpoint is specialized first to one coarse Fourier
mode, then to the selected reciprocal fibre. The literal transposed
stabilized alias coefficient and the fine-volume factor remain explicit;
off-fibre DFT values are proved zero. The pointwise finite-synthesis theorem
then cancels the inverse-volume normalization internally.

No periodization, owner estimate, regional `B0`, or terminal field is
asserted.

## Delimitation

S1–S4 remove the diagonal-carrier ambiguity at the operator and Fourier
endpoint levels. They do not yet reconstruct a point source, invoke the
zero-residue selector, transport to the independent source owner, or produce
the regional Green constant needed for window 15.

## Static verdict

All S1a–S4 gates pass statically. The source-separated Green is built from
the generated inverse pair and identified by uniqueness rather than accepted
as a free physical equality. Promotion remains blocked on Lean elaboration
and axiom audit in the sanctioned remote validation path.

