# SURFACE-CLOSURE RESEARCH NOTES — v3 (2026-07-09e, post-audit)
Status: **(i) proved. (ii) proved for 0 < β ≤ 3.5 (verified criterion; β ≤ 3
"safe" pending certified write-up) — conditional ONLY on the φ-lemma, whose
audit is answered below. Both endpoints structurally resolved. Remaining gap:
compact [3.5, β₀]×[δ,π−δ] for certified interval arithmetic + large-β route.**

## 1. THE φ-LEMMA AUDIT (blocking item — answered)

**Exact Lean statement** (PhiMonotone.lean, repo surface-theorem/ and
papers/phi-lemma/, compiled 2026-07-09, exit 0):

    theorem phi_step_of_recurrences (m b R0 R1 R2 : ℝ)
        (hm : 1 ≤ m) (hb : 0 < b)
        (_hR0 : 0 < R0) (hR1 : 0 < R1)
        (hrec1 : 1 / R0 = R1 + 2 * m / b)
        (hrec2 : R2 = 1 / R1 - 2 * (m+1) / b)
        (hAmos : R1 < b / (m + 1/2 + Real.sqrt ((m + 1/2) ^ 2 + b ^ 2))) :
        ((m-1)/R0^2 + (m+1)*R1^2) / m < (m/R1^2 + (m+2)*R2^2) / (m+1)

**Oracle (verbatim log, LEAN-VERIFICATION-LOG.txt in both folders):**
'amos_calibration'' / 'amos_small' / 'phi_unit_step' /
'phi_step_of_recurrences' all: [propext, Classical.choice, Quot.sound].
No sorry, no admit, no custom axioms.

**HONEST SCOPE (the auditor's suspicion is correct and was already the papers'
stated scope — v2 of these notes dropped the qualifier, now restored):**
mathlib has NO Bessel functions. What is machine-checked is the ordered-field
implication [recurrences + Amos bound ⟹ φ-step], with the analytic inputs as
the NAMED HYPOTHESES hrec1/hrec2/hAmos. The instantiation to I_m(β) is NOT
numerical: hrec1/hrec2 are DLMF 10.29.1 (all real orders), hAmos is the
published Amos/Segura theorem (Amos 1974; Segura JMAA 2011; Ruiz-Antolín–
Segura 2016 Thm 2, shift ν→ν+1), hR1 is I_m > 0. Correct claim everywhere:
**"machine-checked modulo classical Bessel inputs carried as named hypotheses."**

**Term-by-term match with Lema R**: r_m = Ã_m/B̃_m = [(m−1)I_{m−1}² +
(m+1)I_{m+1}²]/(m I_m²) — identical to φ_m (I_m² cancels); m=1: (m−1) kills
the I₀ term on both sides (Ã₁/B̃₁ = 2I₂²/I₁² = φ₁ ✓). Strict (<). Range:
ALL real m ≥ 1, ALL β > 0 — no hidden restriction.

**β-large margin (auditor's r₁,r₂ concern)**: the factorization gives the
EXPLICIT FLOOR φ_{m+1} − φ_m ≥ 2(2m+1)/β² (third term alone). Verified clean:
β=20: φ₂−φ₁ = 0.029625 ≥ 0.015 (ratio 1.975); β=100: 0.001197 ≥ 0.0006
(ratio 1.995 — ratio → 2, the (S−3c)(P−(2m+1)c) term supplying the other
half). The shrinking increments are exactly the 1/β² floor, not a warning sign.

## 2. Auditor's two lemmas: INDEPENDENTLY CONFIRMED
(a) SHARP minor bound: |T_mn(t)| ≤ (pq(q²−p²)/6)·sin³t; re-verified on the 13
pairs up to (10,30), max ratio 1.0 (asymptotically exact). Proof route via
|q·U_{p−1}(c) − p·U_{q−1}(c)| ≤ (pq(q²−p²)/6)(1−c²), per-pair polynomial ⟹
Lean-able (nlinarith below cutoff + crude bound for the suppressed tail).
(b) Adjacent floor: q sin t − sin(qt) ≥ (q−1)sin³t for odd q — confirmed to
q = 151. Adjacent pairs (m,m+1) always have q = 2m+1 odd ⟹ every adjacent
minor CONTRIBUTES −2m|c̃|sin³t (m=1: exactly −4|c̃₁₂|sin³t).
(c) IMPROVED DOMINANCE TABLE independently reproduced: criterion (per sin³t)
β=1.5: −0.372; β=2: −23.81; β=3: −24765; β=3.5: −118533; β=4: +4.0e7 (fails,
genuinely — absolute-value bound blind to oscillatory cancellation of far
pairs). **⟹ W < 0 on (0,π) for β ≤ 3.5 verified; theorem "β ≤ 3 safe" to be
written with certified I_m ∈ [(β/2)^m/m!, ·e^{β²/4}] bounds.**

## 3. Work-order corrections ACCEPTED
- Old item 2 was a false hope: the weight H⊗H(cosψ−cosψ′) is positive for
  ψ<ψ′, so the weighted integrand's sign set = the KM-det sign set already
  mapped. Correct target: integrated corner-mass vs bulk-mass ratio as a
  function of (t,β) — the quantitative form the corner/bulk route needs.
- F_A = Q(positive) FAILS (auditor's data: min Q(Hcos) = −0.029 (β=1),
  −398 (β=5), −7e15 (β=20)). F_A > 0 demoted: it is essentially the λ→0⁺
  edge of (ii), not a cheap intermediate.

## 4. Endpoint package (for Arb compactification)
- E even at 0 (F_A, F_B odd ⟹ E′(0) = 0); at π: F_A vanishes to THIRD order
  (A_∞ = 0), E ~ κ(π−t)² — W vanishes cubically at BOTH ends; interval
  arithmetic only needs [δ, π−δ] + signs of two coefficients.
- **t=0 sign is a φ-lemma COROLLARY (fourth lock, same key)**: e₂ > 0 ⟺
  A₃/A₁ > B₃/B₁ ⟺ Cov_μ(m², r_m) > 0 under μ ∝ m·b_m — Chebyshev's sum
  inequality with TWO INCREASING sequences (m² and r_m; r_m increasing IS the
  φ-lemma), strict. Verified: A₃/A₁ vs B₃/B₁ = 2.52/1.04 (β=1), 4.46/3.53
  (β=5), 15.57/14.78 (β=20). No numerics needed in the proof.
- π-endpoint (κ > 0): alternating series, dominant m=1 term, explicit tail
  bound — finite work, queued.

## 5. Work order v4 (= auditor's v3)
1. ~~φ-lemma audit~~ DONE (this note, §1).
2. Write the β ≤ 3 theorem: adjacent floors (elementary trig proof for odd q)
   + sharp per-pair bound (Lean candidate) + Fubini for the W rearrangement +
   certified Bessel bounds. Target: machine-checked except Bessel hypotheses.
3. Endpoints: draft the Chebyshev corollary (e₂ > 0, no numerics); κ > 0 tail.
4. Two-copy map as corner-mass/bulk-mass ratio (not pointwise sign).
5. Large-β: corner/bulk with DLMF 10.41(ii) certified errors.
6. Literature duties (Graf/Neumann; Dharmadhikari–Joag-Dev; Mardia–Jupp;
   Schoenberg/Karlin cyclic VD) — still blocking paper #5.
Ghost ledger addition: buggy inline print in a verification cell (mixed-β
closure) caught and re-run clean — prints in verification cells must bind
their parameters explicitly.

# ═══ v4 ADDENDA (2026-07-09f, post cancellation-audit) ═══

## A. φ-LEMMA: ACCEPTED by auditor. Writing rules locked:
- hAmos verified by auditor on (m,β) ∈ [1,100]×[0.01,300]; MIN SLACK 2.5e-7 at
  (m=100, β=0.01) — the Segura constant is razor-sharp. RULE: cite
  Ruiz-Antolín–Segura 2016 Thm 2 VERBATIM, ν→ν+1 shift computed in an appendix,
  NO convenience weakenings anywhere in the chain.
- Floor 2(2m+1)/β² independently verified by auditor ([1,25]×[0.5,100]).
- The scope sentence ("machine-checked modulo classical Bessel inputs carried
  as named hypotheses") goes to the paper as-is.

## B. π-ENDPOINT HALF-GIFT (auditor; verified here exactly):
∂_t q1(π,ψ) = −4·s1(π−ψ) (identity on the closed form; checked to 8 digits at
3 points, exact by the series). Hence
  B₁^π = −F_B′(π) = (2/π)∫₀^π s1(π−ψ)(Q²s1)(ψ)dψ > 0 STRICT
— part-(i) machinery at the boundary, Hopf-style. NO tail bounds needed for
the κ-denominator. Remaining at π: c₃ > 0 (alternating numerator) ONLY.
DEAD END (auditor's, logged): kernel shortcut for c₃ fails — s3 = −s1″ changes
sign (s1 not concave at large β).

## C. CANCELLATION AUDIT (auditor's decisive experiment; REPRODUCED here):
Compare adjacent floor vs EXACT far block (cancellation included), per sin³t:
  my reproduction (M=35, 60 t-pts): β=4: far 8.95e7 vs adj 9.15e7 (crit −2e6,
  passes barely); β=6: 4.49e14 vs 2.27e14 (FAILS by +2.2e14); β=10: FAILS by
  +9e27 — while true max W/sin³t stays NEGATIVE (−2.6e7 / −6.9e12 / −1.7e23).
READING: at β ≥ 6 the adjacent-vs-far decomposition fails EVEN WITH PERFECT
far bounds — the far peak and adjacent mass live at the same t and cancel in a
t-coupled way invisible to separated maxima. The minors route is PROVABLY
SATURATED at β ≈ 4–6, not unfinished. Margin decay c ≈ 1.6–1.95 (auditor) —
independent confirmation of the e^{−2.1β} mirror phenomenology.
- Abel route: DEAD (auditor's own proposal, killed by their own data —
  symmetric ledger entry).
- Optional exact treatment of (1,3),(2,4) (T₁₃ = 16sin³t·cos t closed form):
  might push 3.5→~3.8–4; LOW VALUE given saturation at 6; parked.

## D. FINAL TWO-SCALE MAP (no route decisions left open):
1. Minors: 0 < β ≤ 3.5 ✓ (certified write-up "β ≤ 3 safe" pending).
2. Machine: Arb/python-flint on [3.5, β₀]×[δ, π−δ]. CERTIFY E′(t) < 0 or
   W/F_B² (O(1) objects — NOT W, which scales e^{6β}); truncate tails with
   I_m ≤ (β/2)^m e^{β²/4}/m!; trim edges with the endpoint package
   (E even at 0; E ~ κ(π−t)², B₁^π > 0 proven, c₃ > 0 pending).
   Feasible target: β₀ ≤ 30 at dps ≈ 2.2β+20 (the precision warning now has
   theorem-level justification: the certified object is exponentially small).
3. Saddle: β ≥ β₀, rigorous production of the exponential constant c ≈ 2 with
   explicit errors (DLMF 10.41(ii) uniform asymptotics). THE remaining real
   mathematics. Success criterion: reach DOWN to an explicit β₀.

## E. Publication calculus (auditor concurs):
If the saddle does not land within TWO sessions, the partial paper ships:
Thm A (part i, two proofs) + Thm B (part ii, 0<β≤3.5, modulo named Bessel
inputs) + endpoint proposition (Chebyshev corollary; B₁^π; c₃ pending→stated)
+ the e^{−2.1β} quantified conjecture + two-scale roadmap. Literature duties
(§v3-5.6) remain the only non-mathematical blocker.

## Work order v5
1. Saddle skeleton (β large): uniform asymptotics of Ã_m, B̃_m near m ≈ β·x*,
   extract the exponent; target explicit β₀. [real math]
2. Arb harness for [3.5, β₀] in parallel. [mechanical]
3. c₃ > 0 alternating-tail bound; write Chebyshev corollary. [short]
4. Certified write-up of Thm B (β ≤ 3). [writing]
5. Literature pass. [blocker for paper]
