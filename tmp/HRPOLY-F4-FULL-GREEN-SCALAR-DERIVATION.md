# F4 full-G amplitude: static derivation to formalize

Not compiler evidence. Read against the literal definitions on 2026-09-04.
Do not promote this calculation to a regional B0 or a terminal field.

Fix initial source coefficient a>0 and RG ratio L>=2. Set a_* to the CMP85
floor and R=L^(j+1). The pending scalar foundations queue constructs a common
rho at a_*, all four windows, a_j<=a, and P(a_j,rho)<=P(a_*,rho).
The existing floor lemma gives a_*<=a_j. This rho is independent of j and
Kloc,Q, but is chosen for fixed a,L; no all-L uniformity is claimed.

Exact abbreviations from the tree:

- P_* = cmp89Eq246FinePointSourceMomentAmplitudeBound a_* rho.
- A = cmp89Eq246CentralAverageRowReciprocalBound rho.
- S = cmp89Eq248ComplexNoncentralGreenSumBound_draft rho.
- T = cmp89Eq249ComplexNoncentralAliasSumBound rho.
- Qc = cmp89Eq248ComplexNoncentralGreenQuotientConstant_draft rho.
- Z = (tsum over integers of cmp89Eq251OneDimensionalAliasWeight with
  exponent cmp89Eq251AliasSeriesExponent 4 (-1))^4.
- b = cmp89Eq246FinePointSourceBareDiagonalAmplitudeBound = 18*(3*pi)^2.
- H = (2/(1-exp(-rho)))^4 * exp(2*rho).

The central component is A*(P_j+S+abs(a_j)*P_j*T). The correction is
abs(a_j)*Qc*P_j. Positivity of each multiplier must be proved from its
literal definition/window before invoking multiplication monotonicity.
Use a_j>0 to replace abs(a_j), the initial coefficient a for the positive
coefficient factors, and the floor ONLY for P. Define the hybrid constant

    C_* = A*(P_*+S+a*P_* *T) + a*Qc*P_* *Z.

Then the intended bound, before normalization, is

    D(R,1,a_j,rho) <= C_* + 256*b*(R+1)^2.

This is not the false assertion D(a_j)<=D(a_*): the full budget is not
antitone in its coefficient. Its central and correction positive factors
are bounded separately, using the opposite end of the source interval.

For R>=1 the elementary inequality (R+1)^2<=4*R^2 gives the intended
normalized bound

    ownerAmplitude(R,a_j,rho)
      <= H*(C_* *R^-4 + 1024*b*R^-2)
      <= H*(C_*+1024*b)*R^-2.

Preserve the first, sharper split as a named theorem before its second
consequence. In particular do not erase R^-2 by immediately replacing it
with 1. The finite source-point normalization is R^-4 exactly once; the
quadratic alias loss leaves R^-2. Positivity of b and H would make the
final constant strictly positive without an arbitrary +1 padding.

What this would give: an explicit constant independent of source depth for
R^2 times the normalized scalar owner amplitude. What it would NOT give:
the remaining source-flow residue dictionary, a physical spacing/norm
conversion, a fine-site row sum, derivative species, the regional Green
certificate or window15. Those remain F2/F3/F5 and must preserve their
own dimensions; no amplitude estimate changes 20/41 or TermSource=0.

Compilation order after the current scalar foundations PASS: test the
project-free R-power inequality in a minimal Mathlib repro; then prove the
hybrid coefficient inequalities against the literal definitions; only then
instantiate the common source-flow radius. No compiler execution is claimed
for any part of this note.

## Auxiliary normalization checked, 2026-09-04 UTC

The elementary R-power inequalities alone passed the Colab Mathlib repro
at source 995370c162c80694029242785925e7bae08476f4, exit0/11.700545847s,
two exact allowed-trio declarations. The first additive-orientation error
is preserved beside the corrected run under
validation-evidence/f4-normalization-repro-20260904/. This is hot auxiliary
evidence, not a cold seal and not a proof of the hybrid amplitude bound above.
The original final sentence refers to the derivation when first written;
only these two elementary inequalities now have compiler evidence.

## Bounded hybrid diagnostic prepared, 2026-09-05 UTC

The scalar foundations are now cold-sealed (Ledger Addendum1109).
The hybrid draft now includes an exact `#print axioms` for its sole public
bound. It remains uncompiled and outside the root. After the F2-F3 cold
archive is preserved and verified, a separate warm diagnostic may test this
draft without changing that archive or interpreting a hot PASS as a seal.
