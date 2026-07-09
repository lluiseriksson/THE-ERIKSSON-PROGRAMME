# SURFACE-CLOSURE RESEARCH NOTES — v2 (2026-07-09d, post-review)
Status: **(i) PROVED (two proofs; write-up duties listed). (ii): endpoint
structure corrected, λ-window halved, minor-expansion route unlocked by the
φ-lemma, and a SMALL-β UNCONDITIONAL REGIME established (β ≤ 1.5 verified,
β ≤ 1 claimable with certified constants).**

## 0. Framework (as v1; constants now pinned)
Qf(t) = (1/2π)∫₀^π q1(t,ψ)f(ψ)dψ with q1(t,ψ) = 2e^{βcos t cosψ}sinh(βsin t sinψ)
= 4Σ_{m≥1} I_m sin(mt)sin(mψ) ⟹ Q sin(m·) = I_m sin(m·) EXACTLY (the 4 vs 1/2π·π
bookkeeping verified numerically; the derivation 4Σ... belongs in the paper).
K2(φ) = I₀(2βcos(φ/2)) [Graf/Neumann addition theorem — CITE: DLMF §10.23(ii),
Watson §11.3; NOT novel]. H = −K2′ = βsin(ψ/2)I₁(2βcos(ψ/2)).
s1 = (β/2)sinψ e^{βcosψ}. F_B = Q³s1. F_A = Q²(H·cos)-normalized as in v1.

## 1. (i) F_B > 0: PROVED. Write-up duties (reviewer, accepted):
(a) Fubini line for the sum/integral exchange (superexponential decay of I_m);
strictness of the reflection lemma stated as "strict on a set of positive
measure". (b) LITERATURE: the reflection lemma is essentially classical
(symmetric-unimodal preserved under circular convolution: Dharmadhikari &
Joag-Dev, Unimodality Convexity and Applications; Mardia & Jupp, Directional
Statistics; cf. Schoenberg cyclic variation diminishing, Karlin TP 1968 cyclic
chapter). Present as "restated with proof for completeness"; the CONTRIBUTION
is the framework (closed-form q1, eigenstructure, F_B = Q³s1), not the lemma.

## 2. ENDPOINT CORRECTION (reviewer's catch — v1 had an ERROR)
v1 claimed F_A/F_B → "2(−1)+..." at π⁻. FALSE. TRUE: E(π⁻) = 0 EXACTLY:
- Telescoping: A_∞ = Σ(−1)^{m+1} m Ã_m-weights cancels after reindex (verified:
  |A_∞| < 1e-36 machine-exact at β=1,5; the m=1 term dies on the (m−1) factor).
- Symmetric proof: k(π−t, π−ψ) = k(t,ψ) ⟹ ω_π ∝ H(ψ)H(π−ψ)dψ symmetric about
  π/2 ⟹ E_{ω_π}[cos] = 0 (cos odd about π/2).
CONSEQUENCES: E decreases from E₀ := Σ m(m+1)I_m²I_{m+1}² / Σ m²I_m⁴ (exact,
verified to 10 digits; E₀ < 1 STRICT by Cauchy–Schwarz) to 0. The λ-window of
the level-crossing formulation is (0, E₀) ⊊ (0,1) — half the work gone.
COROLLARY TARGET (easier than (ii), numerics ✓ β=1,5,20): F_A > 0 on (0,π).

## 3. MLR wording corrected (v1 overclaimed "route CLOSED")
Pointwise TP₂/SR₂ is SUFFICIENT, not necessary, for variation diminishing:
the circle heat kernel also fails log-concavity near the antipode (any smooth
positive even kernel is log-convex near its minimum — the corner violation was
inevitable, not specific to q1), yet heat flow IS variation-diminishing
(Sturm 1836; Angenent 1988, parabolic max principle over CONTINUOUS time).
Honest caveat for an Angenent embedding here: −log I_m(β) ~ m log m ≠ m², so
Q is not a standard second-order parabolic flow; embedding is nontrivial.
Noted as the only surviving "one-shot" route; HIGH RISK.

## 4. THE MINOR EXPANSION IS UNLOCKED: "Lema R" = the φ-lemma (ALREADY PROVED)
The reviewer's candidate Lemma R (r_m = Ã_m/B̃_m strictly increasing) IS
φ-lemma of papers/phi-lemma (machine-checked, PhiMonotone.lean): the
normalization cancels in the ratio. So ALL minors c̃_mn < 0 unconditionally,
and W(t) = Σ_{m<n} c̃_mn T_mn(t), T_mn = (m−n)sin((m+n)t) + (m+n)sin((n−m)t).

## 5. NEW RESULT: the small-β regime of (ii) (first unconditional piece)
- T₁₂(t) = 3sin t − sin 3t = 4sin³t ≥ 0 exactly.
- BOUND: |T_mn(t)| ≤ (π³/48)·pq(p²+q²)·sin³t on (0,π), p=n−m, q=n+m.
  Proof: f = q sin(pt) − p sin(qt) has f(0)=f′(0)=f″(0)=0 and |f‴| ≤ pq(p²+q²)
  ⟹ |f| ≤ pq(p²+q²)min(t,π−t)³/6 (same at π by parity); sin t ≥ (2/π)min(t,π−t).
- DOMINANCE: W ≤ sin³t·[−4|c̃₁₂| + (π³/48)Σ'|c̃_mn|pq(p²+q²)]. Margins verified
  (mpmath 40d): β=0.2: 1.0e-10 vs 1.5e-14; β=1: 2.4e-3 vs 1.9e-4 (12×);
  β=1.5: 0.39 vs 0.14; β=2.0 FAILS with this crude bound (28.07 vs 28.96).
- THEOREM (to write up rigorously): W(t) < 0 on (0,π) for 0 < β ≤ 1 (safe),
  via certified Bessel bounds (β/2)^m/m! ≤ I_m ≤ (β/2)^m e^{β²/4}/m! and an
  explicit geometric tail estimate. Optimizable toward β₁ ≈ 1.9 with sharper
  per-pair bounds; midrange to be closed later by certified interval
  arithmetic (Arb / python-flint, NOT bare mpmath — reviewer requirement).

## 6. Work order (next session; reviewer's list, adjusted)
1. Write up the small-β theorem with certified constants (β ≤ 1 first).
2. Derive both W-expansions formally; map numerically where the WEIGHTED
   two-copy integrand H⊗H(cosψ−cosψ′)·KMdet is positive (bet: nowhere).
3. F_A > 0 as standalone target (spectral trick: seek F_A = Q(positive)?).
4. Large-β: bulk TP₂ outside O(1/β) corners + H-weight corner suppression
   with DLMF §10.41(ii) certified errors / Amos-ratio machinery (papers/01).
5. Literature pass duties of §1(b) before any paper-5 draft.
DECISION STANDING: paper #5 waits unless (ii) stalls two sessions; if it
stalls, publish (i)+framework+E₀+negatives WITH the literature pass done.
