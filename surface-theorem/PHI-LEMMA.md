# THE φ-LEMMA — PROVED AND MACHINE-CHECKED (2026-07-09)
*(BF2 / Surface Theorem, structural half of the last asterisk C(β,s,ε)>0)*

## Statement
For β > 0, with ρ_j = I_{j+1}(β)/I_j(β) and
φ_m = [(m−1)/ρ_{m−1}² + (m+1)ρ_m²]/m  (m ≥ 1),
which equals A_m/B_m of the π-local expansion (chk363) INCLUDING the m=1 edge
(the (m−1) coefficient annihilates the missing staple), the sequence φ_m is
STRICTLY INCREASING. **Corollary: c_mn = A_mB_n − A_nB_m = B_mB_n(φ_m − φ_n) < 0
for all 1 ≤ m < n.**

## Proof (elementary, same arsenal as the Bessel–Amos note)
1. Eliminate ρ_{m−1}, ρ_{m+1} via the three-term recurrences
   (1/ρ_{m−1} = ρ_m + 2m/β, ρ_{m+1} = 1/ρ_m − 2(m+1)/β). With u = ρ_m,
   c = 1/β, S = u + 1/u, P = 1/u − u:
   m(m+1)(φ_{m+1} − φ_m) = 2m(m+1)·δ, and the EXACT FACTORIZATION holds:
       δ = (S − 3c)·(P − (2m+1)c) + (2m+1)c²
   (algebraic identity; sympy residual 0).
2. P − (2m+1)c > 0 is exactly the unit-step inequality of the Bessel–Amos
   note (Amos bound + calibration — machine-checked there).
3. S − 3c > 0: the Amos bound gives u < β/(a+s) < β/(2a) = β/(2m+1) ≤ β/3,
   hence 1/u > 3/β. QED (strict, all β > 0, all m ≥ 1).

Third time the calibrated Amos bound closes a lock of the programme.

## Machine verification
PhiMonotone.lean (self-contained; Lean 4.30.0-rc2, Mathlib cd3b69b):
  amos_calibration', amos_small, phi_unit_step (the factorization),
  phi_step_of_recurrences (φ_m < φ_{m+1} with hrec1/hrec2/hAmos as named
  hypotheses). Oracle: [propext, Classical.choice, Quot.sound] ×4; no sorry.
Numerics: identity + positivity pieces verified mpmath dps=40 on
β ∈ {0.3, 2, 8, 32, 100, 1000}, m ≤ 11; φ increasing verified k ≤ 200 earlier.

## What remains for W(π−ε) < 0 (the full asterisk)
With c_mn < 0 proved, W = Σ |c_mn| (−1)^{m+n} [q sin(pε) − p sin(qε)] (p=n−m,
q=n+m) and the claim is odd-parity dominance. The parity-mirror cancellation
is ~e^{−2.1β} (see BF2-ATTACK-NOTES.md); route: shift-telescoping
(m,n)→(m+1,n+1) + closed-form k=1 edge anomaly. NEXT TARGET.
