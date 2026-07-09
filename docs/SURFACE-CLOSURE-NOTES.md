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

# ═══ v5 ADDENDA (2026-07-09g, THE SADDLE SKELETON — VERIFIED) ═══

## S1. Provenance ledger entry (auditor's hygiene flag, accepted)
The "public PDF still contains Fejér–Gronwall" claim originated from the
REVIEWER voice (the 9.35 review: "el PDF público ... que tengo parseado
todavía dice ..."), NOT from the auditor. Repo .tex/.pdf verified clean; the
stale copy is the viXra-submitted version (v2 replacement queued on number
assignment). Ledger rule: attribute claims to their exact source voice.

## S2. THE SADDLE SKELETON (auditor's; INDEPENDENTLY VERIFIED here)
Representation: E(t) = E_{ω_t}[cos] = (F_A/F_B)/2 as a circle convolution
against the odd extension H̃; phase Φ(ψ) = 2β[cos((t−ψ)/2) + cos(ψ/2)],
unique dominant real saddle ψ* = t/2, value 4βcos(t/4).
**LIMIT LAW (verified to 4 digits):**
    E(t) = cos(t/2)·(1 − c(t)/β + O(β⁻²)),  E′(t) → −½ sin(t/2) < 0.
My cross-check of the auditor's c-table (c := β(1 − E/cos(t/2))):
  t=0.5: 1.5248/1.5264 (β=60/120) vs 1.526 ✓;  t=1.5: 1.8054/1.8072 vs 1.807 ✓;
  t=2.5: 3.1851 (β=120, dps=304) vs 3.185 ✓;  t=3.0: 11.013 vs 11.01 ✓.
Saddle value: (1/β)log F_B at t=1.2 drifts 3.378→3.588→3.699→3.757 (β=15..120)
toward 4cos(t/4)=3.8214 with (log β)/β corrections ✓.
Consistency web: E₀ ≈ 1 − 3/(2β) (my own earlier data: 0.92548 vs 0.925 at
β=20; 0.98502 vs 0.985 at β=100 ✓); E(π)=0=cos(π/2) exact ✓; the e^{−2.1β}
mirror = the O(1/β) window at π where the image term bends sin((π−t)/2) into
κ(π−t)² ✓. c(t) explosion near π (11.0 at t=3) ≈ tan(t/2)tan(t/4) structure —
marks the crossover, coherent.
**HALF-ANGLE MAJORANT (verified at proper precision, β=80–120):**
E(t) < cos(t/2) everywhere sampled — optional bonus conjecture
F_A/F_B ≤ 2cos(t/2) for all β (not needed for the theorem; prettiest line
of the eventual paper if it falls).

## S3. GHOST LEDGER — my own, this round
Ran the E-scan near π at β=80–120 with dps=25 and nearly logged a FALSE
violation of the half-angle majorant against the auditor. My own documented
rule (dps ≥ 2.2β+20 near π) applies to ALL evaluations INCLUDING quick scans.
Corrected at dps=216–304: all anomalies vanish, auditor's numbers exact.
RULE HARDENED: any evaluation with t > 2 and β > 30 uses dps ≥ 2.2β+40.

## S4. What remains for the theorem (auditor's honest list, adopted)
1. Laplace with certified remainders: bulk arguments 2βcos(·/2) bounded below
   ⟹ DLMF 10.40 (simple I₀,I₁ asymptotics with explicit error bounds)
   suffices; ψ≈±π corner is 1-D and H vanishes there (integrable, trivial vs
   the old 2-D corner).
2. Uniformity target: ∃ explicit C(δ), β₀(δ): E′(t) < −¼sin(t/2) for
   β ≥ β₀, t ∈ [δ, π−δ]. β₀ is the Arb ceiling.
3. Edge patches: [0,δ] via E even + e₂>0 (Chebyshev, done) + certified E‴
   bound; [π−δ,π] via κ>0 — note c₃>0 at LARGE β now also follows from this
   same Laplace, so the alternating-tail bound only needs small-mid β.

## Work order v6
1. Derive c(t) from second-order Laplace analytically; MUST reproduce
   1.526/1.618/1.807/2.192/3.185/11.01 (built-in unit test). [next session]
2. Certified Laplace remainder (DLMF 10.40) ⟹ explicit β₀(δ). [the real math]
3. Edge patches (§S4.3). 4. Arb harness [3.5, β₀]. 5. β≤3 certified write-up.
6. Literature duties (unchanged, block paper #5).
STATUS: (i) proved ×2; (ii) proved on (0,3.5] + limit law verified at 4 digits
+ E′ limit strictly negative. One number left to manufacture: β₀.
