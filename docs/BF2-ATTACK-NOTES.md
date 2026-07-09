# BF2 ATTACK NOTES — C(β,s,ε)>0 / W(π−ε)<0 (Surface Theorem last asterisk)
Session 2026-07-09 (Claude Fable 5). Status: NOT closed; structure extracted.

## Object (from chk363)
r_k = I_{k+1}(β)/I_1(β);  A_{k+1} = r_k² Σ_{j∈{k−1,k+1}∩[0,tmax)} (j+1) r_j²;
B_{k+1} = (k+1) r_k⁴;  c_mn = A_m B_n − A_n B_m;
W(t) = Σ_{1≤m<n} c_mn [(m−n)sin((m+n)t) + (m+n)sin((n−m)t)],  t = π−ε.
Claim to prove: W < 0 strictly for all β in the corridor, all ε ∈ (0, ~0.4].

## Verified structure (mpmath, dps 60–100, truncation-stable)
1. **φ_k := A_k/B_k is strictly increasing in k** (β = 2, 8, 32, 100, k ≤ 200)
   ⟹ **c_mn < 0 for ALL m<n**. Candidate LEMMA, likely provable from
   Turán-type inequalities on r_k (the house Amos/Turán metal). φ_k =
   [k r_{k−1}² + (k+2) r_{k+1}²] / [(k+1) r_k²] — increasing ⟺ ratio
   inequality in r's. START HERE next session.
2. At t = π−ε:  g_mn = (−1)^{m+n+1}[q sin(pε) − p sin(qε)], p=n−m, q=n+m;
   bracket > 0 for ε ≤ π/q (sin(x)/x decreasing). So
   W = Σ |c_mn| (−1)^{m+n} [q sin(pε) − p sin(qε)]: an ALTERNATING-PARITY sum
   of positive quantities. W<0 ⟺ odd (m+n) pairs dominate even pairs.
3. **Near-perfect parity mirror**: even- and odd-class sums agree to relative
   accuracy ~ e^{−cβ}. Measured true totals (high dps): W(β=8, ε=.025) ≈ −2.9e-8;
   W(32) ≈ −5.0e-29; W(100) ≈ −5.1e-95. Fit: **|W| ≈ e^{−cβ}, c ≈ 2.03–2.17**
   (i.e. ~e^{−2β} with polynomial corrections). The ε³-moment parity split shows
   the same: (odd−even)/even ≈ +2e-4 (β=8), +7e-27 (β=32), +1.4e-94 (β=100),
   ALWAYS with odd-dominance (⟹ W<0). WARNING: float or low-dps evaluation gives
   pure noise (ghost-15 class); at β=100 need dps ≳ 100.
4. **Mechanism hypothesis (the route)**: the shift (m,n) → (m+1,n+1) maps parity
   classes into each other; if A,B were exactly shift-covariant the bulk would
   cancel EXACTLY. The defect is concentrated (i) at the k=1 edge (A_1 misses the
   j=−1 staple: A_1 = 2 r_0² r_1² only) and (ii) in the r_k tail. Conjecture:
   W = −(edge defect) + O(tail), edge defect > 0 of size ~ e^{−2β}·poly(β,ε).
   PLAN: write W as telescoping sum over the shift, isolate the k=1 anomaly in
   closed form (products of I_1, I_2, I_3 only), bound the rest by the proved
   unit-step/Turán inequalities. Any estimate-based proof is hopeless (needs to
   beat a 10^26–10^93-fold cancellation); the proof must be structural.

## Numerics reproduction
See this file's session transcript; core snippet in CONTEXT.md §13. Use
tmax ≥ 4β + 100, K ≥ 2β + 60, dps ≥ 2.2β + 20.
