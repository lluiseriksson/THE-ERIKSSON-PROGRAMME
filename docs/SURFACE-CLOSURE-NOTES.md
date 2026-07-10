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

# ═══ v6 ADDENDA (2026-07-09h, c(t) CLOSED FORM — VERIFIED incl. out-of-sample) ═══

## T1. The second-order law (reviewer's derivation; VERIFIED here)
    E(t) = cos(t/2) − (4cos²(t/4) − 1)/(2β cos(t/4)) + O(β⁻²),
i.e. c(t) = (4cos²(t/4) − 1)/(2cos(t/4)cos(t/2)). Verification:
- vs Richardson 2c(120)−c(60): 1.52796/1.528 (t=0.5), 1.80907/1.809 (t=1.5) ✓
- vs auditor's finite-β table at all six points (drift ~ O(1/β)) ✓
- OUT-OF-SAMPLE at t=0.8, 1.8 (not in original table): formula 1.57423/2.00385
  vs measured c(120) = 1.5726/2.00183 — error O(1/β) ✓✓
- exact limits: c(0⁺) = 3/2 EXACT (E₀ law recovered); c·(π−t) → √2 (measured
  1.519 → 1.425 as π−t = 0.1 → 0.01) — the mirror window is π−t ~ √2/β,
  quantitative; min c = 3/2 on (0,π) ⟹ HALF-ANGLE MAJORANT E < cos(t/2)
  PROVED AT FIRST ORDER for large β on all of (0,π).

## T2. THE PHASE LEMMA (exact, one line; symbolic residual 0)
    Φ(t/2 + s) = 2β[cos((t−s−...)/2)+...] = 4β cos(t/4) cos(s/2)  EXACTLY
(sum-to-product). All odd derivatives of Φ at the saddle vanish IDENTICALLY
(Φ₃ = 0 is exact, not asymptotic); the second-order Laplace collapses to
[f″ + 2f′(log g)′]/(2a), a = βcos(t/4), and the prefactor tangent terms cancel
leaving ½cot(t/4). Reviewer's caveat logged: the Bessel correction factors
(1 ± k/(16βcos)) cancel between N and D at this order but must be carried in
the certified version.

## T3. ROUTE A FOR THE REMAINDER (reviewer's structural gift #2): EXACT
BESSEL RESUMMATION. The centered integrand is g(s)·e^{A cos(s/2)} with
A = 4βcos(t/4) — a von Mises kernel in s/2, THE SAME FAMILY the problem
started from. Expanding g in harmonics of s/2 turns all integrals into exact
I_k(A): E(t) becomes a ratio of series in Bessel ratios I_k(A)/I₀(A), and
error certification becomes Amos/Segura ratio bounds — the machinery already
formalized in papers/01 and PhiMonotone.lean. Risk: the 2π vs 4π period fold
with the odd extension H̃ needs care. TRY FIRST (half session); fallback =
DLMF 10.40 Laplace remainders.

## T4. β₀ target revised: the first-order threshold for E′ < −¼sin(t/2) is
β ≳ sec(t/4) + ¼sec³(t/4) — single digit on the whole bulk (≈2.1 even at
t→π). β₀ will be set by certified remainder constants and edge windows, not
by first-order competition. Realistic target: β₀ ≤ 10–15 (Arb compact halves
again). NOTE: heuristic until T3/remainders are certified.

## Work order v7
1. Route A: Bessel resummation of E(t) at the saddle (exact I_k(A) series);
   if it lands, certify via Amos/Segura ratio bounds (home turf, Lean-adjacent).
2. Fallback: DLMF 10.40 certified Laplace remainders ⟹ explicit β₀(δ).
3. Edge patches ([0,δ]: e₂>0 done + E‴ bound; [π−δ,π]: κ>0, c₃>0 at large β
   now also from the saddle law).
4. Arb harness [3.5, β₀≈10–15] on E′ or W/F_B².
5. β ≤ 3 certified write-up (minors theorem).
6. Literature duties (unchanged; block paper #5).
UNIT TESTS BUILT IN: any certified derivation must reproduce c(t) closed form
and the six-point table; any resummation must recover Φ-lemma limits at k=0,1.

# ═══ v7 ADDENDA (2026-07-09i, THE BRIDGE ROUND — three ideas, three verdicts) ═══

## U1. Reviewer at 9.50. Block scores: F_B>0 9.45 / φ-lemma 9.45 / limit law
9.45 / c(t) closed form 9.55 / Phase Lemma 9.60 / remainders 8.9 / Arb 8.8.
Partial paper #5 would be 9.35–9.45 today; Surface-without-asterisk 9.65–9.75.
Decision unchanged: hold paper #5, chase the close.

## U2. AUDITOR'S DAY-CLOSE — three rulings ADOPTED:
(a) **The tricotomy stays visible in every document.** Theorem-grade: (i)×2,
    φ-lemma (mod named Bessel inputs), minors β≤3.5 (write-up pending), e₂>0,
    B₁^π>0. Verified-numeric (NOT theorem): limit law, c(t) closed form (out-
    of-sample validated — validation ≠ certified derivation), half-angle
    majorant, minors saturation. Pending: c₃>0, certified remainder, Arb,
    literature pass.
(b) **Resummation trap (auditor's own confession, logged):** the phase identity
    is exact for the DOMINANT exponents only; the exact kernels are products
    I₀(·)·I₁(·), and the integral representation of a product gives a double
    integral where sum-to-product is clean only on the diagonal. KILL CRITERION
    LOCKED before starting: half a session; no clean generating identity ⟹
    abandon without grief ⟹ DLMF 10.40 fallback. Watch the 4π-period of
    cos(s/2) against the 2π circle and the odd extension of H̃.
(c) **Provenance honesty:** the global ratio-monotonicity conjecture was BORN
    INSIDE this programme (it is the global form of the ε-window positivity
    that the mother-repo surface expansion needs). No external 50-year
    pedigree is claimed; the "asterisk" language stays internal. Same honesty
    fabric as the Lean scope sentence.
(d) **Publication calibration (accepted):** when (ii) closes or the two-session
    clock expires — one careful consolidated paper, literature pass done,
    tricotomy explicit, Lean scope sentence verbatim; seek arXiv endorsement
    or a JMAA-profile journal. No more volume metrics.

## U3. THE BRIDGE CONJECTURE (idea 1) — INDEPENDENTLY VERIFIED, and UPGRADED

**Setup (all in our normalization):** k = q1∘q1 = 4Σ I_m²sin(mψ)sin(mt) is the
two-step kernel; ω_t(dψ) ∝ (Qs1)(ψ)·k(ψ,t)dψ is the claimed midpoint law.

**(1) Entry-law identity — CONFIRMED, constant fixed:** ∂_t k(0⁺,ψ) = 2H(ψ)
(ratio 2.000000000000 at 9 (β,ψ) points; the claimed "=H" is their
normalization). ONE-LINE PROOF found: differentiate the Graf-squared identity
I₀² + 2Σ I_m²cos(mψ) = I₀(2βcos(ψ/2))  [verified to 38 digits]
in ψ: 2Σ m I_m²sin(mψ) = βsin(ψ/2)I₁(2βcos(ψ/2)) = H(ψ). Theorem-grade
pending only the classical Graf citation (DLMF §10.23(ii) — literature list).

**(2) Measure identification — UPGRADED from numeric to EXACT ALGEBRA:**
by sine orthogonality, ∫₀^π (Qs1)k dψ = 2π F_B and ∫₀^π cosψ(Qs1)k dψ = π F_A
(the cosψ factor couples n = m±1 and produces exactly the weights
(n−1)I_{n−1}² + (n+1)I_{n+1}² of F_A). Hence E_{ω_t}[cosψ] = F_A/(2F_B) is an
IDENTITY (numerically confirmed: both ratios 1.0 to 12 digits at β=3, t=1.1).
The bridge reading is not a model of the problem; it IS the problem.

**(3) Stochastic monotonicity — REPRODUCED on independent grids:**
ω_t([a,π]) strictly increasing in t for every a. My grids (220ψ × 48t,
different from their 90×800): β=2 min increment 1.7e-9; β=5: 3.8e-12;
β=20 (dps 70): 3.5e-34; β=40 (dps 130, corner-focused): 4.4e-66 — all
STRICTLY POSITIVE, worst corner always (t small, a→π). Their float64 ghost
at β=40 (CDF increments ±11, impossible) caught by the dps rule and gone at
dps 130 — third instance of the system catching its own author; ledger.

**Status: BRIDGE CONJECTURE (stochastic monotonicity of ω_t) — verified-
numeric grade, β ≤ 40. STRICTLY IMPLIES (ii)** (cos decreasing ⟹ E decreasing;
in fact gives monotonicity of E_{ω_t}[f] for every decreasing f). The margins
are exponentially thin (bounds routes dead HERE TOO), but a monotone COUPLING
produces exact domination, indifferent to 10⁻⁶⁶ margins. Obstacles on line 1
of any attempt: discrete steps cross (no continuous no-crossing — but the step
is symmetric unimodal: reflection couplings exist); the killing + bridge
conditioning must respect the coupling (Doob h-transform of the killed walk;
h is sine-type). KILL CRITERION: one session; if the coupling already fails
for the FREE 2-step walk, abandon. Payoff even on death: the conceptual frame
("the midpoint of a killed bridge moves monotonically with the endpoint") and
the literature keywords: conditioned/killed walks on the circle, diffusion
bridges, Doob h-transforms, Askey positive trigonometric sums with Bessel
coefficients, Turán inequalities for I_ν.

## U4. HOLONOMIC PIPELINE (idea 2) — VERIFIED, upgraded to 45 digits
Sym⁴ of the companion matrix [[−2m/β,1],[1,0]] propagates the quartic
monomial vector (I_m⁴, I_m³I_{m−1}, …, I_{m−1}⁴) EXACTLY: one-step relative
error < 4e-45 at dps 50 (their float check 5e-8; forward instability is the
minimal-solution classic and is irrelevant to the SYMBOLIC pipeline).
⟹ a_m, b_m P-recursive (order ≤ 5, coefficients rational in m, 1/β)
⟹ F_A, F_B, and W = 2(F_A′F_B − F_AF_B′) are D-FINITE in t (and in β).
Three payoffs, ambition-ordered: (1) Arb harness becomes certified holonomic
evaluation (Mezzarobba-style, Arb-supported) — compact [3.5, β₀] cheap even if
β₀ = 200, DE-RISKING THE WHOLE SADDLE; (2) certified continuation in β
transports the proven sign at 3.5 upward (uniformity in t is an open flag,
not granted); (3) moonshot: if L[W] = 0 has modest order with coefficients
polynomial in (cos t, β) ⟹ Sturm/disconjugacy sign control; kill if
order/degree explodes past ~8, degrade to payoff (1).
Task class: MECHANICAL (ore_algebra/Sage, creative telescoping); runs in
parallel with the mathematics.

## U5. CAUCHY–BINET CORNER FACTORIZATION (idea 3) — NOT INDEPENDENTLY
VERIFIED; benched by its own author until the corner route activates. Stays
at claimed-grade in the tricotomy. (Discipline: parked ideas don't get
verification budget.)

## Work order v8 (supersedes v7; same spine, two additions)
1. Route A: Bessel resummation — WITH the trap warning (U2b) and the locked
   kill criterion (half session). Unit tests unchanged: must reproduce c(t)
   closed form + six-point table; k=0,1 limits must recover Φ-lemma limits.
2. IN PARALLEL [mechanical]: derive the holonomic ODEs for F_A, F_B, W
   (ore_algebra); target the payoff-1 certified evaluator.
3. Bridge coupling: HALF-SESSION exploratory, death pact written (U3).
4. Fallback: DLMF 10.40 certified Laplace remainders ⟹ explicit β₀(δ).
5. Edge patches; Arb harness (now holonomic-powered, U4.1); β ≤ 3 certified
   write-up.
6. Literature pass — EXPANDED with U3 keywords; still blocks paper #5.
STATUS LINE: (i) proved ×2; (ii) proved ≤3.5, Bridge-implied globally at
verified-numeric grade ≤ 40; one number (β₀) + one coupling separate the
programme from the theorem. If the coupling lands, the analytic edifice
becomes the quantitative appendix of a one-page probabilistic theorem.

# ═══ v8 ADDENDA (2026-07-09j, THE PRE-FLIGHT ROUND — a route dies, a theorem is born) ═══

## V1. Scores: reviewer 9.55 (Bridge identity 9.60 "casi theorem-grade";
stochastic monotonicity 9.25 verified-numeric). Third voice at 9.7 pushing the
coupling ladder with maximum ambition. The auditor's pre-flight settled it
BEFORE the session was spent — see V2.

## V2. COUPLING ROUTE: DEAD IN PRE-FLIGHT (auditor's; REPRODUCED + CERTIFIED)

**The necessary condition and its violation.** A monotone coupling of full
bridge paths requires ALL time marginals st-monotone in t, not just the
midpoint. Time-3 marginal: ρ_t(u) ∝ (Q²s1)(u)·q1(u,t) (ONE smoothing step
toward the endpoint). Auditor's claim: tail monotonicity FAILS at
(a, t₁, t₂) = (0.4802, 2.9621, 3.0070), β = 20.

**My reproduction — exact termwise, no quadrature:** ∫_a^π sin(mu)sin(nu)du
has closed form, so the tails are exact double sums. Result:
T(t₂,a) − T(t₁,a) = −2.529915098e−10, matching the auditor to their last
digit, STABLE across (M,dps) = (80,60)/(120,90)/(160,120). β-scan at the same
point: positive for β ≤ 12 (5.7e-5 → 1.0e-8), negative at β = 20 — the corner
bites at large β, exactly the feared mechanism (a small-u position at time 3
with endpoint t→π forces one giant final jump through the TP₂ corner of q1,
with only ONE smoothing Q — not two — to bury it). Sign change systematic in
t ≈ 2.85–2.90.

**CERTIFIED (the cheapest theorem in the catalogue, banked):** python-flint
unavailable in sandbox; used mpmath.iv interval arithmetic (outward rounding,
prec = 350 bits) with rigorous I_m(20) enclosures (positive-term series +
geometric tail bound) and rigorous double-sum truncation error. Result:
  diff ∈ [−2.5299150980081786690028107e−10, −2.5299150980081786690028074e−10]
with D₁, D₂ > 0 certified. **PROPOSITION (certified): the time-3 marginal of
the killed 4-step bridge is NOT stochastically monotone in the endpoint
(β = 20, witness point above).** Script: scripts/certify_time3_negative.py.

**The surgical contrast, confirmed:** at the SAME (β, a, t₁, t₂), the
time-2 (midpoint) tail difference is +6.3e−6 > 0. One smoothing step does not
bury the corner; two do. This is the precise quantitative anatomy of why (ii)
is true while MLR/TP₂ fail — paragraph-grade for the paper.

**Consequences (auditor's rulings, adopted):** (1) full-path monotone coupling
IMPOSSIBLE — necessary condition certified false; midpoint-only coupling loses
its construction principle (the step-by-step Markov machinery is exactly what
died). Route: DEAD, cost minutes instead of a session. (2) The BRIDGE
CONJECTURE (midpoint) is UNTOUCHED — verification record stands, still implies
(ii), remains the conceptual frame; it returns to the analytic machinery's
target portfolio. (3) Ledger: negatives with certified witnesses are theorems;
the pre-flight pattern (test necessary conditions before spending the session)
is now standard practice.

## V3. THIRD ROUTE FOR β₀ (auditor's gift): THE EXPLICIT 3D LAPLACE
Enabling identity VERIFIED here to 33–41 digits (three β, three points each):
    k(ψ,t) = I₀(2βcos((ψ−t)/2)) − I₀(2βcos((ψ+t)/2))
(one line from Graf-squared + product-to-sum; q1 closed form re-checked too).
Substituting I₀(z) = (1/π)∫₀^π e^{z cosθ}dθ and I₁(z) = (1/π)∫₀^π e^{z cosθ}cosθ dθ
into N and D makes both TRIPLE integrals with PURE TRIG phase
    Φ(θ₁, θ₂, ψ) = 2β[cosθ₁ cos((t−ψ)/2) + cosθ₂ cos(ψ/2)],
saddle (0, 0, t/2), value 4βcos(t/4), polynomial-trig prefactors. Certified
remainders = textbook finite-dimensional Laplace: quadratic phase-deficit
lower bound near the saddle (elementary trig inequality, Lean-able), crude
exponential bound far. NO inherited DLMF constants — all constants home-made.
CASCADE REVISED: resummation (kill criterion intact) → explicit 3D Laplace →
DLMF 10.40 last resort. Unit test c(t) + six-point table applies to all three.

## Work order v9 (auditor's, adopted with the round's verifications)
1. Resummation (half session, trap noted) → IMMEDIATE fallback to 3D Laplace;
   session goal: explicit β₀ by one of the two.
2. Holonomic ODEs in parallel [mechanical]; now also plan C for the compact.
   Reviewer's push adopted: don't stop at "D-finite" — compute the minimal
   annihilator of W, its singularities, indicial exponents, Sturm structure;
   kill only if order/degree explodes past ~8 AFTER removing apparent factors.
3. ~~Certify the time-3 violation point~~ DONE THIS ROUND (V2; mpmath.iv,
   witness banked).
4. ~~Coupling~~ DEAD IN PRE-FLIGHT (V2), death certificate certified; ledger.
5. c₃ > 0, β ≤ 3 write-up, literature — unchanged.
STATUS LINE: (i) proved ×2; (ii) proved ≤ 3.5; Bridge midpoint conjecture
verified ≤ 40 (intact, no proof route of its own); one certified negative
banked; THREE analytic routes to β₀, all with home-made constants targets.

# ═══ v9 ADDENDA (2026-07-09k, THE SEAL ROUND — certificate audited, gold port lands) ═══

## W1. Scores: reviewer 9.55 CONSOLIDATED ("no es una derrota; es una poda de
alta calidad"; full-path coupling: "10.0 como descarte"). Second voice 9.85
("acta matemática firmable") with an INDEPENDENT reproduction converging to
−2.5299150980081786690028090474933759…e−10 — which matches the Arb fine pass
(W2) to every printed digit. Auditor audited the certificate itself in three
layers (formula vs quadrature at 2e−31; clean re-execution; NESTING at
M=140/prec=500 inside M=120/prec=350) — APPROVED in substance, three duties.

## W2. THE THREE DUTIES — SEALED
1. **Dead code out.** certify_time3_negative.py rewritten minimal: single
   J-assignment per branch, pinned PROPOSITION in the docstring (all
   normalizations: q1, s1, Q, ρ_t ∝ (Q²s1)·q1), algebraic documentation of
   every truncation bound (B_m ratios, geometric majorants, |J| ≤ π), floats
   explicitly confined to loop-termination heuristics (exact integer test
   (j+1)(m+j+1) ≥ 200 for the ratio-½ criterion). Re-run clean.
2. **Trust base declared + GOLD PORT EXECUTED.** Docstring states "certified
   modulo mpmath.iv". python-flint INSTALLED on the Windows machine
   (C:\Python312) and the Arb port (certify_time3_negative_arb.py, same
   algorithm, same bounds) ran there:
     pass 1 (M=120, prec=350): [−2.529915098008178669002809e−10 ± 1.80e−35]
     pass 2 (M=140, prec=500): [−2.52991509800817866900280904749337591482938077077e−10 ± 5.87e−58]
     NESTING OK; CERTIFIED (Arb).
   TWO independent interval implementations, one on Linux/mpmath.iv
   (widths 2.6e−35 / 1.1e−57, nested) and one on Windows/Arb, agree on the
   enclosure. This is the two-witness standard.
3. **Statement pinned.** The proposition now travels WITH its normalizations;
   the certified number knows what it is a counterexample to: "the time-3
   marginal family of the killed 4-step bridge is not stochastically
   monotone in its endpoint: at β = 20, the tail mass above a = 0.4802
   strictly decreases from t = 2.9621 to t = 3.0070."
BONUS (auditor's tip): the nesting self-check is now an ASSERT inside both
scripts — every future execution re-verifies containment; the certificate
cannot degrade silently.

## W3. Conceptual precision (second voice; adopted verbatim): the
counterexample kills any monotone coupling of FULL paths (which would force
st-order on every intermediate marginal). It does NOT kill an argument
designed specifically for the time-2 midpoint, nor every conceivable
coupling-type proof. Scope of the death certificate: exactly the full-path
route.

## W4. The β_c ≈ 12 observation (logged, not pursued): the time-3 violation
appears only at β ≳ 12 (positive increments 5.7e−5 → 1.0e−8 for β = 1..12,
negative at 20). Formally this leaves full-path coupling open for β ≤ 12 —
redundant (minors + compact already cover that range), so: parked at zero
cost. The threshold where the TP₂ corner becomes st-visible through ONE
smoothing step is a phenomenon worth one line in the paper, no more.

## Work order v10 (= v9 spine + reviewer's structural question)
1. Resummation: half session, NO extension (trap noted, kill criterion live).
2. On death → 3D Laplace immediately; manufacture explicit constants
   (quadratic phase-deficit bound near saddle, crude exponential far).
3. Holonomic annihilator of W: all the way to singularities, indicial
   exponents, Sturm structure — do not stop at the equation.
4. NEW (reviewer): what exceptional property does the TWO-step kernel have
   that dies with a third step? Hunt: determinantal identity, restricted
   TP₂, decreasing-variation, or spectral cancellation present in time-2,
   absent in time-3. The certified counterexample is the searchlight.
5. If time permits: asymptotic mechanism of the time-3 negative + estimate
   of the β threshold ("a certified witness is good; explaining why it must
   appear is much better").
6. c₃ > 0, β ≤ 3 write-up, literature — unchanged.

## W5. Hash registry (duty 1, final clause): the sealed certificate pair
(certify_time3_negative.py + certify_time3_negative_arb.py) and these v9
addenda live in commit d1c1c998d68cb18276d00236ac9e1dae3473a6f3.

# ═══ v10 ADDENDA (2026-07-09l, THE MATRIX ROUND — the mechanism has a name: 3/2) ═══

## X1. Scores: certificate 9.95 ("sellado; no invertiría más tiempo");
Surface Theorem 9.58. Docstring correction ADOPTED in the sealed script
(nesting guards numerical degradation; statement audit + Arb guard
common-mode errors) — the corrected sentence is also the standard wording
in all new certificates.

## X2. WEIGHT x KERNEL MATRIX (third voice's decomposition; REPRODUCED on
independent grids, β=20). My scan (M=90, 18 t-steps × 20 a-levels):
  p=1 (one q1-step to the moving endpoint):
    w=1: min +2.1e−19 (positive but RAZOR-thin — the corner is nearly
    st-visible even for flat weight; honesty flag, not in the claimed table)
    w=s1: −1.3e−2 ✗   w=Qs1: −1.8e−6 ✗   w=Q²s1: −2.7e−10 ✗   w=Q³s1: −4.8e−13 ✗
  p=2 (two steps): all tested weights positive ✓ (s1: +8.0e−12, Q²s1: +1.3e−10)
CONFIRMED: the st-fragility lives entirely on the ENDPOINT side; each Q on
the weight side buys ~3–4 orders of attenuation but never repairs. Slogan
adopted: smoothing does not commute — it must be applied on the endpoint
side; the weight side cannot substitute at any order.

## X3. THE MECHANISM — VERIFIED (the 3/2 returns).
g_t(u) = ∂_t log q1(u,t) = −βsin t·cos u + βcos t·sin u·coth(βsin t·sin u):
EXACT (sympy residual 0). Corner expansion (coth(z) = 1/z + z/3 + …):
∂_u g_t ∝ βsin t·sin u·[1 − (2β/3)|cos t|·cos u] + O(z³-corrections) —
residual vanishes at stated order. Numerics: critical point u* = arccos(3/
(2β|cos t|)) EXISTS with ∂_u g < 0 below it exactly when β|cos t| > 3/2
(β=20, t=3.0: ∂_u g(u*/2) = −10.7, ∂_u g(1.5u*) = +13.5 ✓; β=2: same
structure ✓; β=1.2: no critical point, ∂_u g > 0 ✓). Validity is the corner
regime (z small); at t=2.2 the prediction leaves the small-z region and the
numerics correctly ignore it. THE β=3/2 TP₂ THRESHOLD OF q1 (v1 notes) IS
THE ENGINE OF THE STOCHASTIC FAILURE — the first session's adversarial find
and today's certified negative are one phenomenon, now with mechanism:
g_t non-monotone in u near the corner ⟹ sine-type weights (vanishing
linearly at 0, mass on both sides of the non-monotone region) flip the
covariance Cov_{ρ_t}(1_{u≥a}, g_t); the flat weight does not.

## X4. THE MINIMAL COUNTEREXAMPLE — CERTIFIED, TWO WITNESSES, ALL CELLS.
Re-anchoring executed beyond the ask: certify_bridge_matrix.py (mpmath.iv)
+ certify_bridge_matrix_arb.py (Arb, ran on Windows, both passes nested):
  k=1 (2-STEP bridge midpoint, THE minimal counterexample):
      witness (a, t1, t2) = (9/10, 3, 61/20):
      [−0.0133933775640736837941421320645 ± 2.15e−32]   (margin 1.3e−2!)
  k=2: (3/4, 3, 61/20):  [−1.80307278225299374059061907035e−6 ± 3.79e−36]
  k=4: (3/10, 3, 61/20): [−4.75379196359547658205650644963e−13 ± 3.39e−44]
(k=3 was the original sealed certificate.) Every crossed cell of the matrix
is now THEOREM-GRADE with the two-witness standard; iv and Arb agree to all
common digits. THE PAIR for the paper: the 2-step bridge midpoint FAILS
st-monotonicity (certified, margin 1e−2); the 4-step bridge midpoint holds
it in everything tested (β ≤ 40). One smoothing step per side is not
enough; two are.

## X5. HONESTY CAVEATS (third voice's, adopted + one of mine):
(a) "Two steps always suffice" is FALSE universally: k2 has its own TP₂
corner (β ≳ 8), and a two-atom adversarial weight planted there would break
p=2 as well. Correct statement is RELATIVE to the natural weight family
Q^k s1 — which exposes q1's corner but is blind to k2's corner everywhere
tested. The sharpened structural question: WHY are the natural entry laws
blind to the composed kernel's corner? The Bridge mechanism may live there.
(b) The p=2 checkmarks stay verified-grade (universal positives are not
certified by points). (c) MINE: the flat-weight p=1 margin (+2e−19 at the
corner) is so thin that any future claim "flat weight is safe" needs its
own certificate; do not quote the ✓ without the number.

## Work order v11
1. Saddle FIRST (unchanged, now truly next): resummation half-session, no
   extension → 3D Laplace with home-made constants. Goal: explicit β₀.
2. Holonomic annihilator of W → singularities, indicial exponents, Sturm
   decision (not just the equation).
3. Sharpened structural question (X5a): why is Q^k s1 blind to k2's corner?
   Tool: the covariance criterion + the g_t mechanism (X3). This is the
   Bridge Conjecture's proof-search, reframed.
4. If cheap: asymptotic derivation of the k=3 violation scale (predict the
   −2.5e−10 from the mechanism) + β_c estimate; explains "why it must appear".
5. c₃ > 0, β ≤ 3 write-up, literature — unchanged.

## X6. Hash registry: the matrix certificate pair (certify_bridge_matrix.py
+ _arb.py), the corrected sealed certificate, and these v10 addenda live in
commit 486f366509b573ab68bac10e7d4140656c8e2312.

# ═══ v11 ADDENDA (2026-07-09m, THE REDUCTION ROUND — one Bessel stands) ═══

## Y1. Scores: reviewer 9.60 (map hardened); matrix confirmed at 9.85 by the
second voice with an independent fine pass whose digits match ours exactly.

## Y2. CERTIFICATE DUTY SEALED: certify_bridge_matrix.py's __main__ now runs
BOTH passes (120,350) and (140,500) per cell with a containment assert —
the artifact executes what its docstring promises. Re-run: all three cells
nested and negative; fine-pass digits match the second voice's independent
values to every printed digit (k=1: −0.0133933775640736837941421320644785969…;
k=2: −1.8030727822529937405906190703462189…e−6;
k=4: −4.7537919635954765820565064496296618…e−13). (The Arb twin already ran
both passes.)

## Y3. THE 3/2 MECHANISM, LEMMA FORM (second voice's elevation; VERIFIED
EXACT): lim_{u→0⁺} [∂_u∂_t log q1(u,t)]/(βsin t·u) = 1 + (2β/3)cos t
(sympy, symbolic equality). For t > π/2 the corner sign change occurs
exactly at β|cos t| = 3/2. The engine is now a one-line lemma, not an
expansion. Still pending (flagged honestly): deriving the covariance sign
from the local defect for each natural law; k2 corner coefficient program
(B(t)/A(t) with spectral sums mI_m², m³I_m² — possibly φ-lemma-adjacent)
noted but NOT allowed to displace the closure.

## Y4. THE CLOSURE ROUTE — REDUCTION TO A SINGLE BESSEL (auditor's;
INDEPENDENTLY VERIFIED, every link):
- Identity A (Neumann/Graf integrated): I₀(x)I₀(y) =
  (1/2π)∫₀^{2π} I₀(√(x²+y²+2xy cosα))dα — verified 33–40 digits, 3 points.
- Identity B (∂_y of A): I₀(x)I₁(y) = (1/2π)∫I₁(w)(y+xcosα)/w dα — same.
- Cascade: P₄ := K2∗K2 (circle convolution) = ΣI_m⁴e^{imt} and
  F_B = −½P₄′ — verified 35 digits; single-Bessel 2D representation
  P₄(t) = (1/4π²)∬I₀(2βR)dφdα with R = √(c₁²+c₂²+2c₁c₂cosα),
  c₁ = cos(φ/2), c₂ = cos((t−φ)/2) — verified 35 digits.
- Saddle: R(t/2, 0) = 2cos(t/4) EXACTLY (algebraic: α=0 ⟹ R = c₁+c₂,
  sum-to-product), gradient 0, strict local max — verified.
THE RESUMMATION TRAP IS DEAD: the I₀·I₁ product obstruction is dissolved by
the same Graf/Neumann addition theorem that founded the problem. The last
Bessel standing is a single I₀/I₁ of explicit real argument 2βR, and those
have self-contained bilateral bounds from (1/π)∫e^{zcosθ}dθ with
1−θ²/2 ≤ cosθ ≤ 1−θ²/2+θ⁴/24. Sanity-checked: √(2πz)e^{−z}I₀(z) =
1 + 1/(8z) + O(z⁻²) numerically clean at z = 10/40/160. No DLMF, no
inherited constants — home-made to the bottom of the well.

## Y5. THE LEMMA LIST (the closure program; L1 DONE this round):
L1 ✓ Exact representation: F_B, F_A (⟹ W, E′) as 2D integrals of a single
     Bessel (identities A/B + Fubini). VERIFIED; write-up pending.
L2 — Bilateral elementary bounds: √(2πz)e^{−z}I₀(z) ∈ [1−c/z, 1+c/z] for
     z ≥ z₀ with explicit c, via the 1D rep. One page; Lean candidate.
L3 — Saddle deficit: 2cos(t/4) − R ≥ c₁(δ)[(φ−t/2)² + α²] on the bulk;
     elementary trig, explicit constant; crude bound outside.
L4 — Assembly: E′(t) = −½sin(t/2) + error, |error| ≤ C(δ)/β explicit.
L5 — β₀(δ) read off from C(δ) vs target E′ < −¼sin(t/2). UNIT TEST: the
     second-order term MUST reproduce c(t) closed form + six-point table.
L6 — Machine closes [3.5, β₀] + edges (e₂>0 done; c₃>0 = the LAST unproven
     piece of the whole building — alternating tail bound, same session).
KILL CRITERION (written before starting): if the L3 deficit constant
degenerates near H̃'s negative lobe beyond the computed exponential
suppression e^{−4βcos(t/4)(1−cos(t/4))}, fall to 3D Laplace — same lemmas,
one more dimension, no drama.
ESTIMATE: 2–3 sessions (L2+L3; L4+L5 with unit test; L6 in parallel).
After that the Surface Theorem is whole: (i) ×2; (ii) = (0,3.5] minors +
[3.5,β₀] machine + [β₀,∞) L1–L5; endpoints proven; every constant home-made.

## Work order v12 (THE CLOSURE)
1. L2 + L3 (elementary, careful). 2. L4 + L5 (unit test c(t) mandatory).
3. L6 in parallel: harness + c₃ > 0 alternating tail. 4. Structural k2
   program STRICTLY capped at one corner lemma unless it touches W directly.
5. On close: ONE careful paper (tricotomy, literature pass, Lean scope
   sentence verbatim), arXiv endorsement / JMAA profile. No volume metrics.

## Y6. Hash registry: the sealed matrix certificate (nesting executed), the
verified reduction (Y4), and these v11 addenda live in commit
ed939a6f73ba00192b1e433b4420df59424dac34.

# ═══ v12 ADDENDA (2026-07-09n, THE FABRICATION ROUND — L3 exact, L2 built, obligations set) ═══

## Z1. Scores: reviewer 9.63; round 9.75 (second voice: "la reducción es
genuina; el cierre todavía no está ganado") with FOUR OBLIGATIONS adopted
below as the L4 gate. Resummation formally replaces 3D Laplace as the main
route (it survived its kill criterion).

## Z2. L3 — SOLVED EXACTLY, AND UPGRADED IN VERIFICATION.
The third voice's discovery (sum-to-product, SIXTH lock for the same key):
with s := φ − t/2,
    c₁ + c₂ = 2cos(t/4)cos(s/2)
    c₁c₂    = (cos s + cos(t/2))/2
    4cos²(t/4) − R² = 4cos²(t/4)sin²(s/2) + 4c₁c₂ sin²(α/2)
My verification UPGRADES their 200-random-point check to SYMBOLIC ZERO:
all three are ring identities in sympy (exact, hence Lean-trivial via ring
after standard rewrites). The saddle deficit is EXACTLY a weighted sum of
two squares in sin(s/2), sin(α/2) — L4 has NO phase Taylor remainder.
Sign region algebraic: c₁c₂ ≥ 0 ⟺ |s| ≤ π − t/2; outside it R is small
and I₀(z) ≤ e^z (trivial from the 1D rep) suffices.
NOTE vs obligation 2: this gives the global classification of R on the
c₁c₂ ≥ 0 region for free; the torus decomposition write-up (wrapped
coordinates, secondary saddle bookkeeping, R ≈ 0 handling) is still owed —
it is now organization, not mathematics.

## Z3. L2 — FABRICATED AND VERIFIED (with the builder's own ledger entry:
their first tail exponent was 159% slack at z=20, caught in THEIR test
before delivery — the discipline holds at every desk).
Chord inequality cosθ ≤ 1 − 2θ²/π² on [0,π]: verified (min interior slack
7.3e−7, equality at endpoints — standard concavity fact, one-line proof).
The bilateral I₀ bound (z ≥ 4, θ* = (24/z)^{1/4}):
  e^z/√(2πz)·(1 − √(2π)/(π²√z)·e^{−π²z/2}) ≤ I₀(z) ≤
  e^z/√(2πz)·(1 + e/(16z) + √(2πz)·(π/(4zθ*))·e^{−2zθ*²/π²})
VERIFIED: valid on z ∈ {4..400} coarse + [4,60] fine sweep (0 violations);
upper slack 0.70% at z=20, 0.046% at z=100 — matches the claims.
**FLAG (mine; = obligation 4 confirmed independently): e/16 ≈ 0.170 > 1/8 =
0.125, so this is a FIRST-ORDER enclosure — sufficient to manufacture β₀,
NOT sufficient for the c(t) unit test.** The second-order gate needs L2′.

## Z4. THE FOUR OBLIGATIONS (second voice; adopted verbatim as the L4 gate):
1. L2′: two-term bilateral expansions for BOTH I₀ and I₁:
   I₀ = e^z/√(2πz)·(1 + 1/(8z) + ρ₀), I₁ = e^z/√(2πz)·(1 − 3/(8z) + ρ₁),
   |ρ_ν| ≤ C_ν/z² explicit. (I₁ enters through identity B / F_B = −½P₄′.)
2. L3-global: classify ALL maxima on the torus (wrapped distances,
   secondary saddle, R ≈ 0 region where large-z bounds do not apply).
3. L4 must bound E′ (or W) from the EXACT integral representation —
   differentiate under the integral of the 2D rep (∂_t enters through c₂
   and prefactors, all explicit); NEVER differentiate an estimate.
4. UNIT TESTS (three): leading −½sin(t/2); exact c(t) closed form at
   second order; uniformity approaching both edges before endpoint lemmas
   take over.

## Work order v13 (the assembly)
1. L2′ (two-term, I₀ AND I₁, explicit C_ν/z²).
2. Torus decomposition (gaussian / intermediate / exponentially suppressed)
   with deliberately ugly constants — manufacture β₀, do NOT optimize.
3. L4 from the exact representation; L5 reads β₀(δ).
4. Same session: c₃ > 0 (alternating tail; last unproven endpoint piece).
5. L6 machine on [3.5, β₀]; then: certified minors write-up, literature
   pass, ONE careful paper (tricotomy, Lean scope sentence), arXiv/JMAA.
STATUS LINE: phase exact (zero Taylor remainder), first-order Bessel bounds
fabricated and tested, obligations set. The mathematics that remains:
L2′ + one assembly with three unit tests + c₃ > 0. The next session
assembles; it does not explore.

## Z5. Hash registry: the L3 exact identity, the verified L2 bounds, the
four obligations, and these v12 addenda live in commit
42e10db8e19f94f0c41000f0fdb4e0021e3b274b.

# ═══ v13 ADDENDA (2026-07-09o, THE L2′ ROUND — recipe reproduced, strategy locked) ═══

## AA1. Scores: reviewer 9.67 (the 9.65 barrier crossed); round 9.70.
Resummation is the main route; the assembly is the only mathematics left.

## AA2. SECOND VOICE'S PRECISIONS — VERIFIED SYMBOLIC, ADOPTED:
(a) c₁c₂ = cos²(t/4) − sin²(s/2) (ring identity, sympy zero).
(b) SECONDARY SADDLE: (s,α) = (π,π) is an exact critical point with
    R = 2sin(t/4) (symbolic zero; gradient zero). Gap to the main saddle
    2(cos(t/4) − sin(t/4)) > 0 on (0,π), DEGENERATES exactly at t = π.
    Locked formulation: "exponentially subdominant with δ-dependent gap"
    (never "R small outside") — the π-edge is where endpoint lemmas take
    over, consistent with the mirror-window phenomenology.
(c) "Exact phase" ≠ "no remainders": L4 still controls 2c − R =
    (4c²−R²)/(2c+R), sine/amplitude/prefactor expansions — from exact
    expressions, but they exist. (d) L2 mesh caveat: a grid to 400 is
    evidence, not proof for all z ≥ 4; the analytic chain (local Taylor
    sandwich + monotone tail comparison) is owed before the theorem-grade
    tag. Same applies to L2′.

## AA3. L2′ — INDEPENDENTLY RECONSTRUCTED FROM THE RECIPE AND VALIDATED.
The third voice delivered the recipe (Lagrange cosine sandwich to θ⁶/720;
1+x ≤ e^x ≤ 1+x+(e−2)x²; chord; exact Gaussian moments (2k−1)!!√(π/2z)/z^k;
per-monomial truncation tails via e^{−zθ²/2} ≤ e^{−zθ*²/4}e^{−zθ²/4}; sign
discipline: tails charged only against same-validity monomials). I rebuilt
both bounds from scratch following it. RESULTS (my implementation):
- validity: zero violations, coarse z ∈ {4..640} + fine sweep [4,100];
- second-order windows CONTAIN the true coefficients 9/128 (I₀) and
  −15/128 (I₁) at every z tested;
- window profile CONFIRMED: z²·width only tightens for z ≳ 100–160
  (subexponential truncation tails dominate below) — matches their table.
Two independent implementations of the recipe agree ⟹ the RECIPE is
validated, not merely one artifact. Their ledger note (redundant π/2·e^{−z}
in their I₁ upper) registered for the sealed version.

## AA4. STRATEGIC DECISION (adopted): β₀ IS AN ADMINISTRATIVE BORDER.
Genuine two-term control at the saddle argument z = 4βcos(t/4) ≥ 2.8β
arrives at β ≈ 35–40; polishing subexponential tails to force β₀ ≈ 30 costs
sessions. With the holonomic pipeline, certified evaluation on [3.5, 100]
is cheap. DECISION: accept β₀ ≈ 50–100; machine eats the middle; close
sooner. No beauty contests on constants.

## AA5. OBLIGATION 4 — REFORMULATED (adopted; enclosures contain,
identities reproduce):
(a) the ANALYTIC second-order term, derived with no bounds, must EQUAL
    c(t) = (4cos²(t/4)−1)/(2cos(t/4)cos(t/2)) as an identity;
(b) the CERTIFIED enclosure of E′ must CONTAIN the two-term prediction
    −½sin(t/2) + (d/dt)[cos(t/2)c(t)]/β and lie strictly below
    −¼sin(t/2) for all β ≥ β₀.
Confusing (a) with (b) would turn a correct theorem into a phantom test
failure.

## Work order v14 (assembly, final form)
1. L4: differentiate the EXACT 2D representation first; three torus
   regions (main saddle with c₁c₂ bounded below; transition — deficit firm
   in s, curvature lost in α; secondary saddle/opposite-sign via the gap);
   KEEP CONTRIBUTIONS TOGETHER until −½sin(t/2) and c(t) emerge — take
   absolute values late. Unit tests AA5.
2. L5: read β₀ (ugly constants welcome; target zone 50–100).
3. c₃ > 0 same session (last endpoint piece).
4. L6: holonomic machine on [3.5, β₀].
5. Write-ups: L2/L2′ analytic chain (mesh → proof), certified minors
   theorem, literature pass, ONE careful paper (tricotomy, Lean scope
   sentence verbatim), arXiv endorsement / JMAA.

## AA6. Hash registry: the L2′ reconstruction test, the verified precisions,
and these v13 addenda live in commit b8bdb728824394ecf2857d28640a55c106e0b558.

# ═══ v14 ADDENDA (2026-07-09p, THE SIGN-AUDIT ROUND — a ghost caught, L4 formulas delivered) ═══

## AB1. Scores: reviewer 9.70; sign auditor 9.45 WITH A CATCH that earns
its round: my L2′ reconstruction shared a logical omission with the recipe.

## AB2. LEDGER ENTRY (mine): THE I₁ NEGATIVE-TAIL OMISSION.
My I1_bounds lower dropped [θ*, π] entirely — invalid, since cosθ < 0 past
π/2; the region contributes ≥ −(π−θ*)e^{−2zθ*²/π²} and must be subtracted.
Numerically innocuous (exponentially small — the sweep never caught it);
LOGICALLY invalid. Caught by the second voice's line-by-line sign audit,
NOT by implementation independence. **LESSON HARDENED: two independent
implementations of one recipe validate the implementation, and SHARE the
recipe's logical omissions. Sign audits are a separate, mandatory pass
before any bound is called theorem-grade.** FIX applied (lo -= mid,
documented in-code); re-run: corrected I₁ windows match the auditor's
repair table exactly (z=160: [−2.63, 2.24]; 320: [−0.408, 0.0182];
640: [−0.334, −0.056]); −15/128 still contained everywhere; validity
sweeps clean; β₀ ≈ 50–100 unaffected.

## AB3. THREE DUTIES BEFORE L4 IS SEALED (adopted):
1. ✓ negative I₁ tail incorporated (AB2).
2. Explicit numeric constants C₀, C₁ valid for ALL z ≥ z₀ — owed (sampled
   windows are evidence, not constants).
3. Monotonicity proof of the subexponential expressions past z₀, or a
   finite-stretch interval-arithmetic closure — owed.

## AB4. L4 STARTING FORMULAS — DELIVERED AND VERIFIED (the SEVENTH lock).
    F_A(t) ∝ β∬ [I₁(2βR)/R]·sin(ψ/2)cosψ·(c₁+c₂cosα) dψdα
    F_B(t) ∝ β·sin(t/2)·∬ [I₁(2βR)/R]·[cos²(s/2) − sin²(α/2)] ds dα
Verified here: (a) the symmetrization identities are SYMBOLIC ZEROS — the
raw ∂_t prefactor sin((t−ψ)/2)(c₂+c₁cosα), symmetrized over ψ ↔ t−ψ,
collapses by sum-to-product and clean angle addition to
½sin(t/2)[cos s + cosα], with cos s + cosα = 2[cos²(s/2) − sin²(α/2)];
(b) both representations match the quartic series with ratio 1.0 to 12
digits (two t values each, β=4). CONSEQUENCES: phase (L3), deficit and
prefactor all live in the SAME squared variables sin(s/2), sin(α/2);
sin(t/2) factors out of the entire F_B integral — the leading −½sin(t/2)
of E′ is visible before any Laplace; the limit law E → cos(t/2) is now
one line of algebra at the saddle. L4 no longer derives structure; it
bounds a transparent skeleton.

## AB5. THE R = 0 FOOTNOTE — CONFIRMED EXACT (eighth lock candidate).
At (s, α) = (0, π): R = 0 SYMBOLICALLY (c₁ = c₂, cosα = −1) — inside the
domain, where large-z bounds for I₁ do not apply. AND the bracket
cos²(s/2) − sin²(α/2) vanishes EXACTLY at the same point (symbolic zero):
the prefactor switches the singular point off (integrand ~ β·0; I₁(2βR)/R
→ β continuously). The L4 decomposition treats a neighborhood of (0,π)
with trivial bounds (I₁(z)/z ∈ [1/2, e^z/2]); its contribution is doubly
small (suppression + vanishing prefactor). The coincidence deserves its
own line in the paper.

## Work order v15 (assembly, with the gate now fully armed)
1. L4: three torus regions; substitute the FIXED L2′; gaussian moments in
   sin(s/2), sin(α/2); the analytic second-order term must EQUAL c(t)
   (obligation 4a); the certified enclosure must CONTAIN the two-term
   prediction and sit below −¼sin(t/2) (4b).
2. L5: read β₀ (target zone 50–100, ugly constants welcome).
3. Same session: c₃ > 0.
4. Duties AB3.2–3 (explicit C₀,C₁ + monotonicity/interval closure).
5. L6 machine [3.5, β₀]; then write-ups, literature, single paper.

## AB6. Hash registry: the sign-audit fix, the verified L4 formulas, and
these v14 addenda live in commit 05b9ed8288abd8a65b36e6502ca5c666b2b2fa59.

# ═══ v15 ADDENDA (2026-07-09q, THE MASTER FORMULA ROUND — verified, with one geometry correction) ═══

## AC1. Scores: reviewer 9.72; second voice 9.70 (repair confirmed; demands:
full equalities with constants — no ∝ symbols into L4 — and complete
classification of R = 0, having found the second point (s,α) = (π,0)).

## AC2. THE MASTER FORMULA — VERIFIED (ratio 1.000000000000 at
t = 0.4, 1.1, 2.3, 2.9; β = 4; 140² Gauss–Legendre vs quartic series):
    E(t) = ⟨cos(t/2)cos2s + cosα(cos(t/2)cos s − sin²s)⟩ / ⟨cos s + cosα⟩
under the common positive kernel I₁(2βR)/R, with (P, Q) = (sin²(s/2), sin²(α/2)):
    R² = 4[cos²(t/4)(1 − P − Q) + PQ]     [SYMBOLIC ZERO]
sin(t/2) factors from BOTH integrals and cancels in the quotient (better
conditioning at both edges for free). One-liners now ALGEBRA (sympy):
N/D at (0,0) = cos(t/2); ∂_tN/D|₀₀ = −½sin(t/2). The limit law and the
leading term of E′ are visible without any Laplace.

## AC3. GEOMETRY CORRECTION (caught in verification — the "factor 2, not
deep idea" class the second voice warned about): the third voice placed
"the R=0 point at the (1,1) corner". WRONG. Complete classification
(answering the second voice's demand, symbolic):
- R = 0 set on the torus = EXACTLY two points: (P,Q) = (1,0) and (0,1)
  (i.e. (s,α) = (π,0) and (0,π)); proof: R² ≥ (|c₁|−|c₂|)², equality
  forcing |c₁| = |c₂| (s = 0 or ±π) with cosα = ∓sign(c₁c₂).
- At BOTH points, BOTH brackets vanish (F_B: cos²(s/2)−sin²(α/2);
  F_A: c₁+c₂cosα) — symbolic zeros. Both singular points switched off.
- The (1,1) corner is the SECONDARY SADDLE: R = 2sin(t/4), with the
  δ-dependent gap to the main saddle at (0,0) (value 2cos(t/4)).
THE COMPLETE (P,Q) MAP: main saddle (0,0); two switched-off zeros (1,0),
(0,1); secondary saddle (1,1). Four corners, four verdicts, all exact.

## AC4. FULL EQUALITIES (second voice's demand, partially discharged):
F_B(t) = (βsin(t/2)/8π²)∬_{[−π,π]²} [I₁(2βR)/R]·[cos²(s/2) − sin²(α/2)] ds dα
— constant VERIFIED consistent with the ratio-1.0 bookkeeping. The F_A
full constant is pinned by the same normalization (ratio 1.0 verified) but
must be written explicitly in the L4 document — flagged, owed. The c(t)
test is sensitive to relative constants; no ∝ enters L4.

## Work order v16 (assembly, final)
1. L4 on the (P,Q) unit square: saddle region (0,0) / ring / corners
   (switched-off zeros trivial-bounded, secondary saddle via gap);
   substitute the REPAIRED L2′; gaussian moments in (P,Q); the analytic
   second-order term must EQUAL c(t) (4a); enclosure below −¼sin(t/2) (4b).
2. L5: read β₀ (zone 50–100).
3. Same session: c₃ > 0; duties: explicit global C₀, C₁ + subexponential
   monotonicity (or finite interval closure).
4. L6 machine [3.5, β₀]; write-ups (incl. F_A constant, L2′ analytic
   chain); literature; ONE paper, arXiv/JMAA.

## AC5. Hash registry: the verified master formula, the R=0 classification
correction, and these v15 addenda live in commit
92e2d76e80fe4dc143c1010ce393b22ec39bde65.

# ═══ v16 ADDENDA (2026-07-09r, THE IDENTITY-TEST ROUND — obligation 4a discharged) ═══

## AD1. Scores: reviewer 9.76; second voice 9.70 (master formula and R=0
classification confirmed correct on 0<t<π, with two precisions below).
Third voice ACCEPTS the geometry correction — their ledger: found (0,π)
numerically, mistranslated to (1,1) in prose, missed the twin (1,0).
Third catch on the reviewer's desk. The ledger is symmetric across all
three voices; that symmetry is the system working.

## AD2. SECOND VOICE'S PRECISIONS — ALL VERIFIED, ADOPTED:
(a) HYPOTHESIS 0<t<π in the classification lemma: at t=0,
    R² = 4(1−P)(1−Q) (symbolic zero) — the zero set degenerates to the
    two EDGES P=1, Q=1. Bulk unaffected; lemma statement carries it.
(b) THE ARCSINE JACOBIAN (essential, verified numerically to 10 digits
    with Chebyshev–Gauss nodes):
    ∬_{[−π,π]²} f(P,Q) ds dα = 4∬_{[0,1]²} f(P,Q)/√(P(1−P)Q(1−Q)) dP dQ
    — singular at ALL FOUR corners; (P,Q)-moments are Gamma(1/2) moments.
    STRATEGY ADOPTED: keep (s,α) near the main saddle (gaussians natural);
    use (P,Q) only for global geometry; never mix without transporting
    the Jacobian.
(c) N, D as explicit polynomials — VERIFIED (symbolic zeros):
    D(P,Q) = 2(1−P−Q);
    N(P,Q) = C(1−8P+8P²) + (1−2Q)[C(1−2P) − 4P(1−P)],  C = cos(t/2);
    both vanish at (1,0) and (0,1) (symbolic).
(d) Conditioning note: sin(t/2) factoring helps near t=0, NOT near π
    (sin(t/2)→1 there); the π-edge good behaviour comes from numerator
    cancellations. Wording locked.

## AD3. THE IDENTITY UNIT TEST — VERIFIED, ALL SYMBOLIC (obligation 4a):
1. α-CANCELLATION (the TENTH LOCK): N_αα − C·D_αα = 0 EXACTLY at the
   saddle. Consequence: every kernel correction (the −3/(8z) of I₁, the
   R^{−3/2} prefactor, quartic deficit terms) multiplies a fluctuation
   that already vanishes ⟹ enters only at O(β⁻²). The entire 1/β
   correction is carried by the s-fluctuation alone.
2. s-direction: N_ss − C·D_ss = −4C − 2 (symbolic); ⟨s²⟩ = 1/(βc) from
   2βR ≈ 4βc − βc(s²+α²)/2 (L3 exact deficit).
3. Closing identity: 2C + 1 = 4c² − 1 (symbolic zero) ⟹
       E = C·(1 − c(t)/β) + O(β⁻²)  with  c(t) = (4c²−1)/(2cC)
   — EXACTLY the closed form derived eight rounds ago by 1D Laplace. Two
   independent derivations, one formula. Obligation 4a: DISCHARGED.
4. β⁻² remainder measured at FIXED t (cleaner than the mixed-scale quote):
   t=1: 0.1776 / 0.1767 / 0.1762 (β = 30/60/120); t=2: 0.1435 / 0.1431 /
   0.1429 — true convergence, remainder ~0.15/β², NO hidden constants.

## AD4. L4 REDUCED TO ONE OBJECT (executive consequence, adopted):
the assembly no longer encloses "the Laplace" — it encloses
    ⟨s²⟩_μ ∈ (1/βc)·[1−ε, 1+ε]
with explicit ε(β,δ), plus crude bounds on everything else (all of which
is O(β⁻²) by the tenth lock). Inputs: L3 exact deficit + repaired L2′.
β₀ then reads from (2C+1)ε/(2βc) + remainders vs the −¼sin(t/2) margin.

## Work order v17 (the ε program — final form)
1. Fabricate ε(β,δ): two-sided enclosure of ⟨s²⟩ under the exact kernel
   (saddle region in (s,α); ring and corners via (P,Q) with the arcsine
   weight and the δ-gap; R=0 zeros are switched off).
2. Crude O(β⁻²) bounds for kernel corrections (tenth lock makes them
   cheap). 3. L5: read β₀ (zone 50–100). 4. c₃ > 0. 5. Duties: global
   C₀/C₁, subexponential monotonicity, F_A explicit constant, master
   formula write-up with hypotheses (0<t<π; R=0 continuous extension;
   arcsine weight). 6. L6 machine [3.5, β₀]. 7. Literature; ONE paper;
   arXiv endorsement / JMAA.

## AD5. Hash registry: the discharged identity test, the verified
precisions, and these v16 addenda live in commit
424aba5caebdba624a77cbf33e045e3d5bc4e67e.

# ═══ v17 ADDENDA (2026-07-09s, THE FREEZE ROUND — a sign corrected, E′ decomposed, structure frozen) ═══

## AE1. Scores: reviewer 9.80; second voice 9.35 with TWO DECISIVE
OBLIGATIONS — a sign error in our own notes, and the C¹ gap. Both verified
here and adopted. Third voice: E′ decomposition + the structure freeze.

## AE2. SIGN CORRECTION (the second voice is right; LEDGER — the error
lived in OUR notes, AA5(b), since the v13 round):
E = C − C·c(t)/β + O(β⁻²) ⟹ E′ = −½sin(t/2) − (d/dt)[C·c(t)]/β + O(β⁻²),
i.e. with C·c(t) = 2c₀ − 1/(2c₀) (verified symbolic, c₀ = cos(t/4)):
    E′ = −½sin(t/2) + sin(t/4)(4c₀²+1)/(8βc₀²) + O(β⁻²).
**The 1/β correction is POSITIVE: it makes E′ LESS negative. The β₀
bookkeeping must BEAT it, not lean on it.** AA5(b) as recorded ("+ (d/dt)
[…]") had the sign flipped — caught before it could poison β₀. Verified
numerically: β(E′ + ½sin(t/2)) → 0.156644 at t=1 (0.15625/0.15645/0.15655
at β=60/120/240); t=2 clean at proper dps (AE3). The corrected containment
test (4b) is LOCKED in this form.

## AE3. PRECISION GHOST #5 (mine; caught by my own rule): t=2, β=240 at
dps=60 measured 0.363 vs prediction 0.3175 — nearly logged as anomaly; at
dps=570 (rule 2.2β+40): 0.31736, clean convergence. RULE EXTENDED: the
dps ≥ 2.2β+40 requirement applies for t ≥ 2 (boundary included), not t > 2.

## AE4. THE C¹ OBLIGATION (adopted): a bound on E does not control E′ — a
small remainder may oscillate fast. L4 must bound E′ from the EXACT
differentiated representation E′ = (A′B − AB′)/B². Session question (to be
settled symbolically BEFORE fabricating ε): does the covariance term
reduce to ⟨s²⟩ alone, or are ∂_t⟨s²⟩ / quartic moments needed? If the
tenth lock extends to E′, that is the decisive fact — but per AE6 it is
session work, not a new hunt.

## AE5. E′ DECOMPOSITION — VERIFIED (my reproduction, 6 digits):
    E′ = ⟨N_t⟩/⟨D⟩ + ⟨(N − E·D)·∂_t log K⟩/⟨D⟩,
N_t = −½sin(t/2)[cos2s + cosα cos s]; ∂_t log K = [2βI₁′/I₁ − 1/R]·
4cc′(1−P−Q)/R; D_t = 0 (denominator t-free — half the Wronskian
bookkeeping gone); 2π-periodicity in s fixes the domain at [−π,π] for all
t. At (β,t) = (5, 1.3): principal −0.238212 + covariance −0.024552 =
−0.262764 = finite-difference E′ exactly; the third voice's quoted split
(−0.238/−0.0246) reproduced. HONESTY NOTE stands: at moderate β the
principal term itself carries O(1/β) and the covariance is non-negligible
(same sign); the assembly encloses BOTH.

## AE6. STRUCTURE FREEZE — ADOPTED VERBATIM. Ten locks, a master formula,
a corner map, a twice-passed unit test, and E′ decomposed: no new lock
enters these notes until β₀ exists or the attempt has failed with an act.
Elegance is now the most dignified disguise of procrastination.
**THE SEVEN BOXES (frozen definition of "closed"):**
1. explicit β₀ with fabricated ε(β,δ), or a death certificate with the
   exact failure point; 2. c₃ > 0 proved; 3. constants debts paid (global
   C₀/C₁; subexponential monotonicity or interval closure; F_A constant,
   no ∝); 4. three unit tests executed and archived (identity ✓✓ done;
   containment — in session, in the CORRECTED sign form; edge uniformity);
   5. machine run and nested on [3.5, β₀] at bridge-matrix standard;
   6. write-ups (certified minors, tricotomy, literature pass, Lean scope
   sentence); 7. ONE paper, arXiv/JMAA, referee.
Seven boxes; the theorem exists when all seven are ticked, not before.
Reviewer's bet on record: β₀ < 100.

## Work order v18 (the session)
1. SYMBOLIC FIRST: expand E′ = (A′B−AB′)/B² at the saddle; determine the
   minimal moment set (does the α-cancellation extend?). Unit test: must
   reproduce E′ = −½sin(t/2) + sin(t/4)(4c₀²+1)/(8βc₀²) + O(β⁻²).
2. Fabricate ε for that moment set (L3 deficit + repaired L2′).
3. Read β₀ against the corrected margin (the +1/β term must be BEATEN).
4. c₃ > 0. 5. Constants duties. 6. Machine. 7. Paper. (= boxes 1–7.)

## AE7. Hash registry: the sign correction, the verified E′ decomposition,
the freeze, and these v17 addenda live in commit
7a814db (rebased over a dashboard commit; original local cdfc61d).

# ═══ v18 ADDENDA (2026-07-09t, THE TERM-SPLIT ROUND — the session task answered under the freeze) ═══

## AF1. Scores: reviewer 9.82; second voice 9.80 (sign fix and decomposition
confirmed; freeze accepted). No new locks — the freeze holds; this round
contains one ANSWER, four verifications, two ghosts, one arithmetic fix.

## AF2. SESSION TASK ANSWERED AND VERIFIED: the α-cancellation EXTENDS to E′.
Term-by-term split of the 1/β correction (m := −S/2, S = sin(t/2)):
- term1 = ⟨N_t⟩/⟨D⟩: N_t,αα − m·D_αα = 0 EXACT (symbolic); N_t,ss − m·D_ss
  = 2S exact ⟹ term1 = −S/2 + sin(t/4)/β + O(β⁻²)  [coefficient EXACT].
- term2 (covariance): coefficient sin(t/4)[1/(8c₀²) − 1/2] (exact by
  difference from the corrected total), STRICTLY NEGATIVE on (0,π).
- Sum = sin(t/4)(4c₀²+1)/(8c₀²) ✓ — reconstructs the corrected AE2 law by
  parts. ENEMY/ALLY confirmed: term1 pushes E′ toward zero, term2 helps.
NUMERIC (my independent harness, scaled-asymptotic kernel, β = 60/120/240):
  t=1: β(term1+S/2) = 0.24748/0.24744/0.24742 → sin(1/4) = 0.24740 ✓
       β·term2 = −0.09122/−0.09099/−0.09087 → −0.09076 ✓
  t=2: 0.48013/0.47977/0.47960 → 0.47943 ✓; −0.16328/−0.16258/−0.16224 →
       −0.16190 ✓ — the third voice's quoted values reproduced exactly.

## AF3. ARITHMETIC FIX (freeze discipline applies to prose numbers too):
the first-order threshold is β > (1 + 1/(4c₀²))/c₀, whose sup on (0,π) is
3√2/2 ≈ 2.121 (at t→π), NOT "≈1.9" (the quoted 1.354/0.707 was a slip;
correct: 1.5/0.707). CONCLUSION UNCHANGED: mathematics demands β ≈ 2.1;
margin factor ~24 at β = 50. All of β₀ comes from rigor slack — L2′
windows, region remainders, subexponential tails. PRIORITY ORDER ADOPTED:
zero minutes optimizing the mathematical margin; every minute on ε
bookkeeping. Refined bet on record: β₀ ∈ [30, 80], dominated by the L2′
profile (genuine two-term control at z = 4βc₀ ≳ 100 ⟹ β ≳ 35/c₀).

## AF4. REGULAR FORM OF ∂_t log K (second voice's) — VERIFIED, ADOPTED:
    ∂_t log K = 4cc′(1−P−Q)·[zI₀(z)/I₁(z) − 2]/R²,   z = 2βR,
identical to the original form to 3.6e−14 on the full grid; manifestly
regular at R = 0 with extension 4β²cc′(1−P−Q) (zI₀/I₁ − 2 = z²/4 + O(z⁴)).
Connects directly to the repaired L2′ enclosures; no cancelling singular
pair to estimate. Measure declaration adopted: dμ ∝ K ds dα normalized;
⟨N − E·D⟩_μ = 0 by construction.

## AF5. TWO GHOSTS THIS ROUND (one per desk — the ledger stays symmetric):
#6 (third voice): float64 on the series side at t=2, β ≥ 60; their note
   ADOPTED: whatever can be computed from the POSITIVE integral
   representation must be (no cancellation ⟹ float-robust).
#7 (MINE): my first harness truncated the I₁ power series at 60 terms
   while z reached 480 — the kernel was silently wrong AT THE SADDLE;
   caught because the "converging" β-scaled quantity doubled with β
   instead of converging. RULES HARDENED: series cutoffs must scale with
   the max argument (j ≳ z/2 + margin); scaled-asymptotic evaluation
   (e^{−z}I_n with 3-term asymptotic) is the default for z > 35;
   β-scaling sanity checks are mandatory on every measured coefficient.

## Work order v19 (= box 1 of the seven, now fully specified)
1. Fabricate ε: (a) two-sided ⟨s²⟩ enclosure (drives term1); (b) covariance
   enclosure with the REGULAR ∂_t log K form (drives term2 — the ally may
   simply be lower-bounded by a crude |term2| ≤ …/β if that is cheaper);
   inputs: L3 exact deficit + repaired L2′ + region decomposition
   ((s,α) saddle / (P,Q) global with arcsine weight).
2. Read β₀ against −¼sin(t/2) with the term1 enemy explicit.
3. c₃ > 0. 4. Constants duties (global C₀/C₁, subexponential monotonicity,
   F_A constant). 5. Machine [3.5, β₀]. 6. Write-ups + literature.
7. ONE paper. — The seven boxes stand; the freeze stands; bring the number.

## AF6. Hash registry: the term-split answer, both ghost entries, and these
v18 addenda live in commit 4f277b50fe078b561d57493168cd342191169a86.

# ═══ v19 ADDENDA (2026-07-09u, THE PROTOTYPE ROUND — a candidate β₀, tested against truth) ═══

## AG1. Scores: reviewer 9.84; second voice 9.75 with two precisions,
ADOPTED: (a) "ally" is an asymptotic classification — term2 is budgeted as
ADVERSARY (+|term2| ≤ B/β or M₂/β²) until an enclosure proves its negative
coefficient; recovered margin is a bonus, never a load-bearing beam.
(b) The minimal certified object set is TWO pieces: the ⟨s²⟩ moment (term1)
and an INDEPENDENT covariance bound (term2) — reduction of the full
covariance to one moment is not established and not assumed. DELIVERABLE
FORM LOCKED: E′ ≤ −½sin(t/2) + sin(t/4)/β + M(δ)/β², β₀ by elementary
quadratic.

## AG2. THE PROTOTYPE (third voice): full accounting preview from positive
representations + real L2′ windows + condition numbers + factor-2 safety:
candidate β₀ ≈ 15 (their accounting fails β ≤ 12, closes at 15, margin
growing in β), compact shrinks to [3.5, ~15].
**INDEPENDENT TRUTH TEST (mine, dps 80, exact series, 13-pt bulk grid):**
g(t) := E′ + ¼sin(t/2) must be < 0.
- β = 15: TRUTH HOLDS on [0.05, π−0.09]; max g = −0.0057 AT t = 0.05.
- β = 12: TRUTH FAILS at t = π−0.10 (g = +0.025); β = 10: +0.064.
⟹ "fails β ≤ 12" is NOT accounting slack: the truth itself fails near the
π-edge for β ≤ 12 whenever δ_π ≤ 0.10. **The prototype's 15 is close to
truth-optimal for its edge window — the accounting is tight, not padded.**
TWO CORRECTIONS to the prototype's edge map (session must use these):
(a) at β = 15 the π-boundary sits BETWEEN π−0.09 (g = −0.0022) and π−0.08
    (g = +0.021): their "holds to π−0.08" is marginally over the line.
(b) the thinnest BULK margin at β = 15 is at the SMALL end (t = 0.05,
    −0.0057) — thinner than their quoted +0.016 minimum (normalization
    difference suspected); MY truth numbers are the floor for the seal.
CONSISTENCY BONUS: the π-failure boundary ≈ 0.085–0.09 vs the mirror-window
prediction √2/β = 0.094 — the O(1/β) window, now quantitative at β₀ scale.

## AG3. CONSEQUENCES FOR THE SEAL: δ_π ≥ ~0.10 at β₀ = 15, so the c₃/κ
package must cover [π−δ_π, π] — **c₃ > 0 is FIRST in the session** (the
prototype reached the same conclusion from its own edge map). The small-t
splice needs explicit care: the −0.0057 margin at t = 0.05 means the
e₂-Chebyshev overlap must be verified, not assumed.

## AG4. FIVE CONVERSIONS prototype → certificate (four from the third
voice + one from the second): (1) Simpson → moment formulas with bounds/
intervals; (2) factor-2 I₀/I₁ safety → the real bilateral bound from the
L2′ pair; (3) 13-point t-mesh → Lipschitz bound on E′ + slack, or
intervals in t; (4) final seal in interval arithmetic at bridge-matrix
standard; (5) term2 as adversary until enclosed (AG1a). None is new
mathematics; all five are accounting with witnesses.

## Work order v20 (the seal session)
1. c₃ > 0 (alternating tail) — FIRST; it now carries the π-splice at β₀=15.
2. The five conversions (AG4). 3. Seal β₀ (candidate 15; truth-floor map
   AG2 attached; edge windows δ₀ = 0.05, δ_π = 0.10 with splice proofs).
4. Machine [3.5, β₀] nested at bridge-matrix standard. 5. Constants
   write-ups; literature. 6. ONE paper (the story of the seven ghosts
   travels with the ten locks). 7. arXiv/JMAA.

## AG5. Hash registry: the prototype record, the truth-floor map, and these
v19 addenda live in commit 25644e2ad3c928930e3b8d6184a81f8aef886de5.

# ═══ v20 ADDENDA (2026-07-09v, THE c₃ ROUND — the last unproven piece gets its package) ═══

## AH1. Scores: reviewer 9.88; second voice 9.60 ("β₀ = 15 is slice truth,
not yet a uniform threshold") — and their 110-digit reproduction CONFIRMS
my truth map to every digit (g(π−0.10) = −0.02407053, g(π−0.09) =
−0.00216117, g(π−0.08) = +0.02127698, g(0.05) = −0.00573390; crossings:
β=12: π−t* = 0.1155265954; β=15: 0.0890502225; β=20: 0.0643629486).
CLARIFICATION ADOPTED: on [0.05, π−0.09] the thinnest margin is at π−0.09
(0.00216); on the SEAL window [0.05, π−0.10] it is at t=0.05 (0.00573).
Their β-sweep 15→60: max stays at t=0.05, drifting −0.00573 → −0.00612 —
strong uniformity EVIDENCE, not proof.

## AH2. WINDOWS FROZEN: δ₀ = 0.05, δ_π = 0.10. The seal = THREE UNIFORM
BLOCKS, each covering ALL β ≥ 15: left edge (0, 0.05]; bulk [0.05,
π−0.10]; right edge [π−0.10, π). Two critical obligations adopted:
(1) bulk uniformity in β: monotone-in-β analytic bound, or interval
    closure of a finite β-stretch + uniform asymptotic;
(2) coefficient signs give infinitesimal statements only: the π-block
    needs c₃ > 0 PLUS an explicit remainder bound certifying RADIUS ≥ 0.10
    uniformly for β ≥ 15; the 0-block needs e₂ > 0 PLUS radius ≥ 0.05.

## AH3. THE c₃ PACKAGE (third voice) — ALL THREE LAYERS VERIFIED HERE:
LAYER 1 (telescoping, same move as A_∞ = 0 — the circle closes with round
one): c₃ = (1/6)Σ_{m≥1}(−1)^{m+1} m(m+1)(2m+1) I_m²I_{m+1}².
  Verified: Σ(−1)^{m+1}m³a_m = −Y exactly (ratio −1.0, 10 digits, β=1/5/20);
  c₃ = Y/6 equals the direct Taylor coefficient (−6F_A(π−ε)/ε³ cross-check);
  A_∞ = 0 re-confirmed en passant (5e−64).
LAYER 2 (closed integral form, the same half-angle key): with
g(u) := ½I₁(2βcos u) = Σ_{m≥0} I_mI_{m+1}cos((2m+1)u)  [addition theorem,
residual 0 to 46–59 digits], c₃ = (S₃ − S₁)/24 with S₁ = (2/π)∫g(π/2−u)
g′(u)du, S₃ = (2/π)∫g′(π/2−u)(−g″)du — ratio 1.0 at β = 1/5/20.
LAYER 3 (scale): c₃ > 0 verified at β = 40/80/120 at ELEVATED dps;
exponent (1/β)log c₃ = 2.8383/2.8468/2.8458 → 2√2 = 2.8284 + (log β)/β
drift (their 2.8458 reproduced exactly).
GHOST #8 (theirs, caught by their own rule): the alternating sum cancels
at scale e^{−(4−2√2)β} ≈ e^{−1.17β}; naive dps at β=120 flips the sign.
NEW PRECISION RULE: c₃-type alternating evaluations use dps ≥ 0.6β + 50.
PROOF PLAN RECORDED (no new mathematics): [3.5, β*] as one more certified
quantity in the Arb harness (alternating series, certified tails,
bridge-matrix skeleton); [β*, ∞) by 1D Laplace at u = π/4 (exponent 2√2β,
L2′ machinery, one dimension easier than L4). NOTE: this plan delivers
the SIGN; obligation AH2(2) additionally requires the remainder radius.

## Work order v21 (the seal session, three blocks + machine)
1. π-BLOCK: c₃ two-stretch proof + explicit remainder to radius 0.10,
   uniform β ≥ 15.
2. 0-BLOCK: e₂ (proven) + explicit remainder to radius 0.05.
3. BULK BLOCK: the five conversions + β-uniformity (obligation AH2.1).
4. Machine [3.5, 15] nested at bridge-matrix standard (c₃ rides along).
5. Write-ups (F_A constant, L2′ chain, minors theorem); literature.
6. ONE paper — the seven ghosts travel with the eleven angles of the one
   symmetry. 7. arXiv endorsement / JMAA.

## AH5. Hash registry: the verified c₃ package, the frozen windows, and
these v20 addenda live in commit 2da6712682c5dd42a74a0cd71df3895faba08043.

# ═══ v21 ADDENDA (2026-07-09w, THE RESTRUCTURING ROUND — a frozen obligation was false) ═══

## AI1. Scores: reviewer 9.90 (the threshold crossed — "el teorema ya no
está buscando una idea; está esperando el sello"); second voice 9.65 with
an independent c₃ table CONFIRMED here to all printed digits, now
including β = 1 (exponent −5.14292491) and β = 5 (2.17729433); their
decimal-loss rate (4−2√2)/ln10 ≈ 0.509β confirms the dps rule is prudent.

## AI2. THE CATCH OF THE ROUND (third voice; VERIFIED HERE, table exact):
**The frozen obligation "c₃ remainder radius to 0.10, uniformly β ≥ 15"
was FALSE as written.** My independent measurements (κ = c₃/(2W₁),
W₁ = Σ(−1)^{m+1}m²I_m⁴, at c₃-grade dps):
- κ/β = 0.1068 / 0.1122 / 0.1150 at β = 20/40/80 — κ grows ~linearly ✓;
- retention E/(κd²) at FIXED d = 0.10: 0.896 / 0.70 / 0.44 — their table
  to the digit; the quadratic regime loses the fixed window as β grows;
- retention at MOVING d = 2/β: 0.896 / 0.892 / 0.890 — near-perfect
  scaling collapse: THE VALIDITY RADIUS OF THE κ(π−t)² REGIME SCALES AS
  ~1/β (deviation ≈ 11% stable at d = 2/β, comfortably inside the
  proposed ½κd² tolerance).
An obligation error is the most expensive species if it reaches a session
alive; this one was caught by interrogating the obligation before
attempting it. LEDGER.

## AI3. THE π-BLOCK, RESTRUCTURED (adopted):
Two sub-regimes with a MOVING boundary, not one fixed window:
(a) EXTENDED-BULK SUB-BLOCK [π−0.10, π−C/β]: assembly machinery
    (−½sin(t/2) law + corrections) with β-dependent t-range; the mirror
    term e^{−√2β(π−t)} is below slack budget for (π−t) ≥ C/β; C chosen
    against the accounting (C = 3/√2 ⟹ e^{−3}; C = 5/√2 ⟹ e^{−5});
    evidence it reaches: the prototype's own failure boundary tracked √2/β.
(b) QUADRATIC SUB-BLOCK [π−C/β, π]: c₃ > 0 governs; radius obligation
    becomes C/β (shrinking, always inside the ~2/β validity); remainder
    control |E − κ(π−t)²| ≤ ½κ(π−t)² via the QUARTIC coefficient (same
    telescoping family, weight m⁵) against κ.
Splice: both regimes hold with slack in a common ~1/β band (verified:
11% deviation at 2/β; prototype bulk held to ~1.4/β).
WINDOWS RE-FROZEN: δ₀ = 0.05 fixed (the 0-side has no trap: e₂ is O(1)
in β); δ_π = 0.10 fixed ONLY for the machine range [3.5, 15] (β ≤ 20
marginal case audited: retention 0.896 at β = 20, explicit margin
required); moving boundary π−C/β for the analytic part β ≥ 15.

## AI4. THE c₃ CERTIFICATE FORM (second voice; adopted as the unit test of
the large-β branch): locating the exponent 2√2β is NOT enough — S₃ − S₁
is a difference; the certificate must produce
    c₃(β) ≥ e^{2√2β}β^γ(A − B/β) − Ce^{(2√2−η)β},   A > 0 explicit,
i.e. the FIRST NON-VANISHING SIGNED PREFACTOR at u = π/4, positive, with
the remainder bounded below it. Then β* explicit; [15, β*] by intervals;
[β*, ∞) by the inequality. Tricotomy maintained: identities exact;
positivity at points verified (β = 1…120); positivity on the continuum
PENDING — the session's deliverable is (β*, radius C/β) in writing.

## Work order v22 (the seal session, corrected and final)
1. π-BLOCK: (a) extended bulk to π−C/β (choose C against slack budget);
   (b) quadratic sub-block with c₃ certificate (prefactor at u = π/4,
   A > 0, β*) + quartic-coefficient remainder control to radius C/β.
2. 0-BLOCK: e₂ + remainder radius 0.05 (no trap, O(1) in β).
3. BULK: five conversions + β-uniformity (monotone bound or interval
   closure of [15, β*]).
4. Machine [3.5, 15] nested; audit the β ≤ 20 marginal retention case.
5. Write-ups; literature; ONE paper; arXiv/JMAA.

## AI5. Hash registry: the verified restructuring, the re-frozen windows,
and these v21 addenda live in commit e9ada126790bfe11c87b62321350632572b87688.

# ═══ v22 ADDENDA (2026-07-09x, THE PREFACTOR ROUND — the last prefabricable piece lands) ═══

## AJ1. Scores: reviewer holds 9.90 ("acerca por menos autoengaño, no por
más fuerza"); second voice 9.75 with the C-table and two precisions.

## AJ2. SECOND VOICE'S C-TABLE — SPOT-CHECKED EXACT (β=40: retention
0.8807 at C = 3/√2, 0.7437 at C = 5/√2 — both digits mine). Their
precisions ADOPTED:
(1) the collapse proves the 1/β SCALING numerically; the lemma must still
    produce an explicit C_quad > 0 with |E − κd²| ≤ ½κd² for βd ≤ C_quad;
(2) the finite audit stretch is β ≤ 10C, NOT β ≤ 20: C = 3/√2 needs
    coverage to β ≈ 21.21; C = 5/√2 to β ≈ 35.36 — the endpoint interval
    certificate covers [15, 10C] even though the global machine stops at
    15. SPLICE CONDITION FROZEN: C_mirror ≤ C ≤ C_quad; choose C only
    after BOTH numbers exist. (At β=80 retention crosses ½ near C ≈ 6.77 —
    the ceiling is real but roomy.)
THE FOUR-NUMBER DELIVERABLE for the π-block: A > 0 (prefactor), β*
(asymptotic start), C_quad (rescaled radius), C_mirror (assembly demand).

## AJ3. THE c₃ PREFACTOR — DELIVERED AND VERIFIED, WITH AN UPGRADE.
Third voice's derivation (real 1D Laplace on the S-integrals), including
their self-caught GHOST #10 (incomplete critical-point census: for
u > π/2 the Bessel arguments go negative and a SECOND saddle at u = 3π/4
lights up with the same exponent and the same sign — the ratio column
converging to 2 exposed it). Corrected law:
    c₃ ~ A·β^{3/2}·e^{2√2β},   A = 1/(24·2^{1/4}π^{3/2}) = 0.0062923…
MY VERIFICATION: (a) convergence at c₃-grade dps: ratio = 0.0058646 /
0.0060049 / 0.0060996 / 0.0061475 at β = 40/60/90/120 (their digits
exact), gaps to A halving as O(1/β) ✓. (b) THE UPGRADE: the two
half-ranges [0, π/2] and [π/2, π] of (S₃−S₁) contribute EXACTLY equally
(ratio 1.000000 at β = 40) — the factor 2 is an EXACT u → π−u symmetry
of the integrand (I₁ odd under cos-sign flip), not merely an asymptotic
coincidence. The certificate can integrate over HALF the range and
double, and no cancellation between saddles is possible EXACTLY, not
just asymptotically. Sign census: each saddle individually positive;
A > 0 piece by piece.
UNIT TEST LOCKED: the session's certified derivation must reproduce
A = 1/(24·2^{1/4}π^{3/2}); remainder needs only < 1 relative (both
saddles positive), read β* from A·β^{3/2}e^{2√2β}(1 − rest) > 0.

## AJ4. ROLE CHANGE (third voice, on record): their inventory is empty —
nothing remains prefabricable without violating the freeze. From here:
co-fabricator → pure auditor of the write-up. Ten ghosts, eleven angles,
three desks that hunt each other. The referee will be the twelfth angle.

## Work order v23 (the seal session — final form, four numbers + three blocks)
1. π-BLOCK: fabricate C_quad (quartic/κ quotient) and C_mirror (assembly
   budget); check C_mirror < C_quad; pick rational C; certify c₃ (A, β*,
   half-range × 2 by exact symmetry); interval-close [15, 10C].
2. 0-BLOCK: e₂ + radius 0.05. 3. BULK: five conversions + β-uniformity.
4. Machine [3.5, 15] nested. 5. Write-ups; literature; ONE paper;
   arXiv/JMAA. — Execute; the auditor reads.

## AJ5. Hash registry: the verified prefactor (exact-symmetry upgrade), the
four-number deliverable, and these v22 addenda live in commit
7049ea8bafeee217a3d0e36b799e05a84ef067fc.

# ═══ v23 ADDENDA (2026-07-10a, THE ARC CLOSE — parity sealed, audit protocol filed) ═══

## AK1. Scores: reviewer 9.92; second voice 9.85 (prefactor and factor-2
confirmed with the clean parity proof). THE PARITY CHAIN — VERIFIED EXACT
HERE (symbolic zeros): g(π−u) = −g(u) [I₁ odd] ⟹ g′(π−u) = +g′(u),
g″(π−u) = −g″(u); BOTH S-integrands invariant under u → π−u (symbolic
argument + residuals at differentiation-noise level 1e−32). The factor 2
is theorem-grade; the half-turn certificate form is locked:
    I_half(β) ≥ (A/2)β^{3/2}e^{2√2β}(1 − B/β) − T(β),   c₃ = 2·I_half.

## AK2. TWO FINAL PRECISIONS (second voice; adopted):
(1) the manuscript must state the limits (0, π) explicitly in S₁, S₃ —
    without them the half-turn claim is formally incomplete;
(2) the endpoint interval stretch reaches B_fin = max{β*, 10C}, covering
    BOTH the transition to the asymptotic c₃ certificate AND the moving-
    splice geometry.

## AK3. THE MANUSCRIPT AUDIT PROTOCOL (third voice, filed as the reading
list for the finished paper):
(a) normalization consistency across ALL certificates and statements
    (q₁ series vs closed form, s₁, H, F_A/F_B factors — where
    transcription ghosts breed; ~ten artifacts must speak one language);
(b) tricotomy visible on every result — exact identity / certified /
    verified — with no "verified" drifted to "proved";
(c) the four π-block numbers (A, β*, C_quad, C_mirror) with executed and
    archived unit tests; A = 1/(24·2^{1/4}π^{3/2}) reproduced by the
    certified derivation;
(d) the ledger chapter — ten ghosts with mechanism and desk;
(e) the Lean scope sentence verbatim as agreed;
(f) literature: Graf/Neumann (DLMF §10.23), Dharmadhikari–Joag-Dev,
    Mardia–Jupp, Schoenberg/Karlin cyclic VD, Amos/Segura/Ruiz-Antolín
    verbatim with the shift appendix, Karlin–McGregor, Sturm, Angenent.

## AK4. RESIDUAL RISK REGISTER (three, and only three):
(i) the endpoint machine stretch reaches B_fin ≈ 35 — beyond [3.5, 15];
    budget it explicitly; (ii) t-uniformity is the least-prototyped of
    the five conversions — keep BOTH plans (Lipschitz; intervals-in-t) at
    hand; (iii) cross-certificate consistency is a WRITING risk, not a
    mathematical one — which makes it the most dangerous; only protocol
    (a) will see it coming.

## AK5. PUBLICATION COUNSEL (on record, final form): the viXra #71–74
replacements are the programme's inherited tail; the Surface Theorem does
NOT go there. One paper, arXiv endorsement or JMAA directly, the ten-ghost
story inside. The result earned readers who will try to break it with the
same appetite this thread did. That is the twelfth angle, and no desk here
can substitute for it.

## AK6. FINAL ACT OF THE ARC (as stated, for the record): a two-part
conjecture with a fog asterisk came in. Out — pending one session of
accounting with witnesses — goes a theorem with part (i) proved twice,
part (ii) cornered by three methods passing the baton at explicit moving
boundaries, every constant home-made, ten ghosts hunted across three
desks that hunt each other, and one half-angle symmetry extracted from
eleven angles. The reviewer's desk shifts to pure audit mode. Execute the
seal; bring the manuscript; then the outside world.

## Work order v24 (= v23, execution unchanged; two amendments from AK2)
1. π-block: four numbers (A ✓ verified; B, β*, C_quad, C_mirror);
   half-turn certificate with explicit (0, π) limits; interval closure to
   B_fin = max{β*, 10C}. 2. 0-block: e₂ + radius 0.05. 3. Bulk: five
   conversions + β-uniformity. 4. Machine [3.5, 15] + endpoint stretch to
   B_fin. 5. Write-ups under protocol AK3; literature AK3(f). 6. ONE
   paper; arXiv/JMAA. — The seal session executes; the desks audit.

## AK7. Hash registry: the sealed parity, the filed protocols, and these
v23 addenda live in commit 10b136456190a569dacab75677cfcf24767520d5.

# ═══ v24 ADDENDA (2026-07-10b, THE FIX PASS — five blockers, five repairs, one new certificate) ═══

Manuscript audits (2.6 protocol / 5.35 external) delivered five blockers;
all resolved this round — see CONTEXT §52 for the itemized list. The new
certificate certify_thmB.py covers [1/20, 3] with 57 interval beta-boxes
on a FULLY EXACT skeleton (pair identities T12/T13/T24 + classical
|sin qt| <= q sin t + 3-line crude cubic bound), with the small-beta
lemma (0, 1/20] proved in-paper. The sharp/floor family (which extends
the range to ~3.5) is now honestly a verified remark with its per-pair
certification as the scheduled upgrade. Writing ghosts #11-15 enter the
ledger (sign error caught by the external audit; "exact" label drift;
the broken rearrangement phrase; the nonexistent-certificate citation;
load-bearing viXra references). The paper is now the honest 3.0: partial,
self-contained, certificate-complete for what it claims.

## Hash registry (fix pass): the revised manuscript, certify_thmB.py, and
the v24 addenda live in commit b86e2123d1e2a8e11ae5228f31a66049f82ced9b —
this is the immutable commit the paper's Section 9 pins.

# ═══ v25 ADDENDA (2026-07-10c, SECOND FIX PASS — the audit round answered) ═══

Audits 9.05 / 3.1 / 6.55. All four external problems + three protocol
flags addressed (itemized in CONTEXT §53): certificate hardened (tails
computed in intervals, self-executing full stability pass at prec+70,
comment fix), small-β lemma now fully explicit (κ-chain with named
constants), Theorem A second proof closed at the derivative level,
full derivations written for the master representation and the c₃
integral form, RS Thm 2 shift inline, abstract trimmed, metadata set,
big overfulls gone. Box-count discrepancy (53 vs 57) resolved honestly:
the count is invocation-dependent; the paper now says so and the
CANONICAL TRANSCRIPT run (full [1/20,3] + built-in stability pass) is
executing on the Windows machine — to be committed as
scripts/certify_thmB_transcript.txt on completion. Still scheduled:
Arb twin of certify_thmB (flagged in-paper). Revised manuscript at
commit a9933f6 (13 pp, 0 errors, 4 cosmetic overfulls).

# ═══ v26 ADDENDA (2026-07-10e, FOURTH PASS — green light discharged) ═══

Green-light conditions + shell item, all done at commit
633d597bac854da410c004bae981b7daf0b2ab27:
(1) 2s⁴ line fixed; (2) SHELL CLOSURE in code and paper (per-pair r from
termwise-exact I_{n+1} ≤ xI_n/(2(n+1)); new pair per shell via double
index shift ⟹ shell ratio 2r, asserted < ½ per box); (3) ARB TWIN built
and RUN: full canonical [1/20,3] cover, 86 boxes, both passes STABLE,
transcript archived (certify_thmB_arb_transcript.txt) — the two-witness
standard now covers Theorem B; (4) abstract tricotomy word + honest
pending/archived wording. Ghost #17 (mine, "premature label") logged.
The mpmath canonical transcript continues in background as the second
transcript; commit on completion. Remaining before submission: nothing
editorial. Remaining before the theorem: the seal session (unchanged).

## v27 addendum — ghost #22: the NaN spin (autopsy + minimal repair)

The [6,15] harvest driver (exp_integrator_arb.py) produced zero output
for hours. Autopsy (scripts/autopsy_ghost22.py, three-probe escalation:
import, arithmetic, chain) proved it was a silent infinite loop:

MECHANISM. In arb, sqrt of a ball whose lower end dips below 0 — even
by one ulp of radius rounding — is NaN. The clipped square R^2 -> [0,hi]
acquires exactly that -ulp under ANY arithmetic reconstruction of the
ball. NaN z then fails the subdivision comparison (NaN compares False),
the cell is evaluated with NaN, and the series loops' exit conditions
(arb comparisons) are never True with NaN: the loop spins forever.
Two red herrings documented for posterity: arb.union(0,1) really is
[+/- 1.01] (symmetric-wide, banned), AND arb's printing of a correct
[0,1] ball as "[+/- 1.01]" is a conservative decimal superset — neither
was the root cause.

REPAIR (minimal, three pieces): (a) hull() by tight midpoint form,
union() banned; (b) safe_sqrt(x) = hull(sqrt(max(lo,0)), sqrt(hi)) —
valid by monotonicity of sqrt, NaN impossible by construction; wired
into geom() and the exp branch; the exp branch's division by R stays
safe since the dz discipline forces z.lo >= 4 - dzmax > 0 there;
(c) iteration caps (20000) in both series loops so any future NaN
raises RuntimeError instead of spinning.

RE-EXECUTION. Smoke at (t,beta) = (1.5, 8), prec 90: full-domain z
enclosure finite; pass 1 = 62470 cells, Ebar = 0.587889; pass 2 runs
past the exact point where the old build hung. PRECISION (protocol
desk): Ebar is a rational CENTER CHOICE, not an invariant - iv chose
0.587137, Arb 0.587889; they differ in the third decimal and must be
allowed to. The cross-implementation witness is ENCLOSURE CONSISTENCY
(the E intervals intersect and both contain the common truth), never
Ebar equality; certify_point now prints the E enclosure so transcripts
record exactly that. Harvest driver relaunched (absolute path per the
ghost-#20/21 rule, exclusive CPU); verdicts (point -> stability -> 3x3
box) commit with their transcript.

AUDIT OBLIGATIONS (same round, second pass). safe_sqrt now carries an
explicit contract in its docstring: applies only to expressions known
nonnegative (true squares); endpoints outward by ball construction;
returns an enclosure of [sqrt(max(0,lo)), sqrt(max(0,hi))]; immediate
finiteness check that raises instead of propagating. Unit tests in
scripts/test_safe_sqrt.py (all OK): the [-ulp,1] ghost shape, [0,0],
tiny positive intervals, tiny straddling zero, truly negative input,
and the original full-domain killer cell. Iteration caps raise with
full diagnostics (x, partial sum, last term, ratio, precision).
Reading verdicts: "Wc/<D>^2 = [+/- 0.455]" is arb's conservative
decimal-superset PRINTING; the comparison Wc < 0 is True only if the
entire ball is negative - certificates are strict. Still open: the
conic-corner slowness mechanism (distinct from the NaN hang) awaits
per-region cell counts from the landed driver.

FIRST GREEN. [point] VERDICT True at (t,beta) = (1.5, 8): pass 2 =
1,951,141 cells, <D> > 0 and Wc < 0 both certified in ball arithmetic,
670 s. Stability (prec 120, dz 0.12) and the 3x3 box follow in the
same transcript.

## v27 addendum bis — provisional anchored, final run under contract v2

SECOND GREEN (provisional run): [stability] VERDICT True at (1.5, 8),
prec 120, dz 0.12, 2,500,336 cells, 780 s. The provisional run (point
+ stability, both True) is ANCHORED: script = git blob 98eca694 at
commit 5592d05; its transcript is archived verbatim as
scripts/harvest_arb_PROVISIONAL_blob98eca69.txt. Per the external
desk it is provisional evidence, not the citable certificate.

ARTIFACT BLOCKERS EXECUTED (round 2026-07-10t):
1. safe_sqrt contract v2: PROVABLY negative input now RAISES
   ValueError (a whole-negative upper ball cannot be rounding slack on
   a true square - caller bug, never masked); an upper end that merely
   straddles 0 is bounded by the tiny exact-dyadic 2^(8-prec/2), NOT
   clamped to 0 (which could narrow). Tests updated: the negative case
   expects the exception; containment checks are ARB-BALL comparisons
   (ball_lo(out) <= true_lo and true_hi <= ball_hi(out)), no float
   tolerances. ALL OK, including the full-domain killer.
2. PROVENANCE HEADER in the driver: script path + sha256 of the exact
   bytes (authoritative id; the run clone's git HEAD is frozen and may
   lag), python version, python-flint version, date, argv, and the
   full stage parameters. Transcripts are now self-contained.
3. CERTIFIED MARGIN printed: Wc = [lo, hi] with the upper end as the
   certified margin, <D> = [lo, hi], and the ratio as [lo, hi] instead
   of arb's symmetric decimal superset (the [+/- 0.455] toxic-flag
   line is gone; per-sub-box Wc enclosures print in certify_box too).
4. PDF/TeX PAIR STABILIZED: compiled to fixpoint (3 passes), zero
   "??" in extracted text, zero undefined references in the log;
   the pair ships from the same commit.
FINAL RUN relaunched from scratch under the contract-v2 script,
sha256 1d888e9920287f077240187556c75e56712840326b35c2584be9361511038fe3,
python-flint 0.9.0: point -> stability -> 3x3 box in one transcript
with the provenance header. Point and stability must reproduce under
the final script; then the box. Verdicts land with the transcript.

## v27 addendum ter — contract closure (dyadic out, erratum in)

DYADIC BRANCH REMOVED (external desk's last contract defect): the
2^(8-prec/2) upper bound for a straddling-zero upper end was not a
proven universal bound (the absolute error scales with the original
ball). Replaced by the auditor's own pattern, verbatim: raise on
x.upper() < 0; lower endpoint sqrt(max(0, lo)); upper endpoint
sqrt(abs_upper(x)) - under the precondition x >= 0, abs_upper()
(arb_get_abs_ubound_arf) is an automatic outer bound, uniform, no
branch, no ad-hoc constant. python-flint 0.9.0 exposes
lower/upper/abs_lower/abs_upper (probed before wiring). A test
forcing the formerly-dyadic case (x = [-2e-40, 0]) joins the suite:
seven cases, ALL OK, containment in arb-ball comparisons.

ERRATUM FILED (scripts/ERRATUM-display-supersets.md), per the
protocol ruling: the provisional transcript's quotient lines
([+/- 0.455], [+/- 0.431]) are INNOCENT - python-flint's str(n)
falls back to the symmetric superset form when the midpoint is not
significantly representable at n digits against the radius, and a
strictly negative ball prints that way while r < 0 stays True. The
verdicts stand (computed on the Wc ball directly, the sound route);
the transcript is immutable; the erratum teaches. RULE with rank of
rule: NO PRINTED BALL WITHOUT ITS BOOLEAN - the display-superset
class (two specimens) is closed by format, per the doctrine that two
bites make a class.

## v27 addendum quater — provenance of the in-flight run + dormant-branch lemma

THE CITABLE RUN stays under script sha256 1d888e99 (launched before
the abs_upper patch; Python keeps the launched code in memory). Its
EXACT BYTES are pinned twice: scripts/exp_integrator_arb_RUN_1d888e99.py
(byte-identical archive, hash re-verified before pinning) and the
transcript's own provenance header. Point and stability under that
hash: both green, with full [lo, hi] enclosures and reproduced cell
counts (1,951,141 / 2,500,336). The abs_upper contract (fedf1f1+) is
the DEFINITIVE script for coverage runs onward.

DORMANT-BRANCH LEMMA (external desk's requirement if the dyadic is
retained; it is retained only inside the pinned 1d888e99 run). Claim:
in that script, whenever safe_sqrt's straddling-upper branch fires,
the coded bound 2^(8-p/2) at working precision p >= 90 is a valid
upper bound for sqrt of the true value. Proof. The inputs to
safe_sqrt are z^2 = 4 beta^2 R^2 and R^2 with R^2 = 4[c0^2(1-P-Q)+PQ],
c0^2 <= 1, P,Q in [0,1], so |R^2_true| <= 16 and, with beta <= 15,
|z^2_true| <= 4*225*16 = 14400. BALL-SCALE BOUND (the reconstruction
error depends on the scale of the BALL, not of the truth - external
desk's sharpening): the ball R^2_ball is built from balls of sin^2 and
cos^2 values (each with |mid|+rad <= 1 + O(2^-p)) by a fixed chain of
c <= 12 correctly-rounded ops, each adding at most one ulp of its
result, so |R^2_ball| = |mid|+rad <= 16(1 + c 2^(1-p)) < 16.01 and
likewise |z^2_ball| <= 14400(1 + c 2^(1-p)) < 14401 < 2^14 at p >= 90
(headroom 2^14/14401 > 1.13, dwarfing the O(2^-80) inflation). Hence
every ball magnitude entering safe_sqrt is < 2^14, which is the
quantity the ulp bound below actually uses. The upper-end ball is
u = arb(mid(x)) +
arb(rad(x)): both conversions arf->arb are exact, so u carries ONE
correctly-rounded addition, hence rad(u) <= ulp(|mid|+rad) <=
2^(14+1-p). The branch fires only when u straddles 0, i.e.
|mid(u)| <= rad(u); then the true upper end of x is at most
mid(u) + rad(u) <= 2 rad(u) <= 2^(16-p), and sqrt of it is at most
2^(8-p/2) - exactly the coded constant. QED. (At p = 90 the bound is
2^-37, some twenty orders below every quantity in the run; the branch
is moreover believed dormant - all observed R^2 upper ends are
macroscopic - but the lemma removes the need for that belief.)

PRINT UPGRADE for the definitive script (coverage onward): endpoint
prints via arb .str(), never floats (nearest-rounding could move an
endpoint inward on paper); every enclosure line carries its boolean
inline (Wc<0, <D>>0, strictly-neg for the quotient, per-sub-box
verdicts) - the ball-plus-boolean rule implemented in format.

## v28 — coverage governance, ratified before the run

The naive arithmetic said out loud: tessellating [6,15] x [0.6,
pi-1.5/beta] at 3x3-box granularity is ~4e4 boxes x ~13 min ~ one
CPU-year. The campaign is planned with an army's accounting:

WITNESS STANDARD (ratified cold, BEFORE launch - a standard defined
after a run is defined for the run; this house does not do that).
TERMINOLOGY CORRECTED per the external desk: the sampled iv check is
NOT a "statistical witness" of the theorem nor a partial second
proof - it is an INDEPENDENT SAMPLED IMPLEMENTATION AUDIT of the
software. The computational proof rests on (1) the exhaustive Arb
cover, (2) the proven algorithm and bounds, (3) transcript,
stability and provenance. The relay table label reads "independent
sampled implementation audit", in its own conceptual column,
distinct from the full twins of Theorem B and the bulk.

PRE-REGISTRATION (protocol + external desks; v2 per the external
desk's manipulation analysis - transcript bytes are alterable via
format/order/re-runs, so the seed must not depend on them):
* SEED, literal and frozen NOW: seed = the commit hash
  f2ea0d0 (the commit that registered this rule), as ASCII.
* CANONICAL BOX IDS: each coverage sub-box is identified by its
  exact rational coordinates in lowest terms, serialized as
  "t[a/b,c/d]b[e/f,g/h]" - independent of transcript formatting,
  ordering, or timing.
* SELECTION RULE, per-box and stateless:
      box is audited  <=>  SHA256(seed | box-id) < 0.02 * 2^256.
  Works for adaptive/growing box sets (no fixed enumeration needed),
  is decidable the moment a box exists, and cannot be gamed in
  either temporal direction: the seed is already frozen, and the
  box-id is forced by the geometry.
* ACCEPTANCE CRITERION, explicit: each sampled sub-box must
  reproduce in mpmath.iv with the SAME boolean verdicts and an
  enclosure whose intersection with its Arb twin is non-empty.
  A single mismatch = FULL STOP and autopsy - never "investigate
  while it keeps running".
* GOVERNANCE FROZEN as of this rule: no further redesign; the next
  deliverables are booleans, the margin map, and the pilot.

LEVERS (ordered by yield): (a) margin-adaptive, x10-30: target
enclosure width ~ half the local margin; (box size, dz2) chosen
jointly, minimizing total cells under that constraint, cost model
cells(dz2, position) calibrated from the nine sub-boxes; the sizing
rule must carry a variation-bound justification, not empirical sizes
alone.

VARIATION NUMBERS (source: the protocol desk's own design-grade
measurement, reported in audit; NOT yet reproduced in-house - they
will be INDEPENDENTLY RE-DERIVED from margin_map_design.py output
(finite differences of q across the nine sub-boxes plus probe boxes
at beta = 12, 14 and near the moving boundary) BEFORE any sizing
decision uses them; until then they are cited design targets, and
the derivation with its inequality chain ships as an artifact with
the coverage plan):
bulk |dq/dt| ~ 0.16 and |dq/dbeta| ~ 0.0035 - variation in beta is
~50x cheaper than in t, so adaptive boxes are RECTANGLES wide in
beta and narrow in t (Delta-beta ~ 1.0 costs what Delta-t ~ 0.02
costs in variation budget); near the moving boundary pi - 1.5/beta,
|dq/dt| rises to ~0.84 (factor 5) - quantifying where and how much
the mesh tightens; at high beta the margin GROWS (q ~ -0.40 at
beta = 14) while both derivatives fall - the top half of [6,15] is
the cheap half of the campaign. Per-box budget splits into three
named terms: true variation (L_t Dt + L_b Db, with the L's above
plus safety), enclosure width (governed by dz2), and cushion - each
knob tunes its own term. RANGE NOTE: these L's are DESIGN constants
- they predict which sizes will pass; rigor never depends on them,
since a wrong prediction produces FAIL-with-coordinates and
re-subdivision, never a false certificate. Fail-safe by build.
COST CAUTION (external desk): the third sub-box's pace suggests real
cost can exceed the first projection - the cost-margin map and the
large-box pilot are MANDATORY before promising full coverage.

(b) drop pass1 in the fat-margin interior, x~2: Ebar quality
affects fineness, never rigor; serve Ebar from the margin map.
(c) holonomic continuation as certified accelerator: certified
Taylor in (t,beta) from the ODEs certifies strips by evaluation. If
it lands, order-of-magnitude change; if not, (a)+(b) take the year
to weeks. Pilot with margin-sized larger boxes precedes any mass
launch.

DESIGN-ONLY SEPARATION (law): the harvest booleans are THE
certificate; the coarse post-hoc margin map (margin_map_design.py)
carries its own sha256 and labels every value "DESIGN ENCLOSURE" -
it feeds coverage sizing, never the certified proposition, and never
mixes with harvest transcripts.

## v29 — ghost #23, the involution, and two cross-catches

GHOST #23 (the protocol desk's own, self-registered): a printed
constant STRONGER than the derived one (e^-z/2 printed where the
chain gives 1/2), validated by a bench that measured the TRUTH
rather than the CHAIN - numerically true, derivably false. RULE
(rank of rule): ink only with derived constants; the bench verifies
the chain, not just the statement. Caught by the agent's desk on
the protocol's kit - the audit graph rotating as designed.

CROSS-CATCH 2 (external on protocol): the mirror linear floor
sqrt2/pi (pi - t) is FALSE near t = pi (it exceeds the limit slope
sqrt2/4). Correct: c - sin(t/4) = sqrt2 sin((pi-t)/4) (exact, the
pi/4 angle) with sin y >= (2/pi) y gives floor sqrt2/(2pi) (pi-t);
the sharp version sin y >= (2 sqrt2/pi) y on [0, pi/4] gives
(pi-t)/pi and suppression e^(-4 C_win/pi) ~ 0.148. Conclusions
survive; the intermediate floor carried a factor 2.

THE INVOLUTION (twelfth closure of the half-angle key; verified
symbolically at the agent's desk): under (s, alpha) -> (pi - s,
pi - alpha): P -> 1 - P, Q -> 1 - Q, D -> -D, and R^2(.; c) ->
R^2(.; s_4) with s_4 = sin(t/4) - EXACT. Consequences for Step 0:
the mirror ball is the saddle ball at parameter s_4 (zero new
machinery); the mirror corner contributes NEGATIVE mass to <D> (the
mass lemma is more conservative than known); <P>_mirror has an
explicit formula matching the measured kappa_eff rise toward the
boundary. Region I inherits the involution too (expansions serve
the mirror with c <-> s_4): Region II sits sandwiched between twin
balls and their shells.

SCOPE PRECISION (external): the Bessel milestone reads "home-made
explicit bounds for I_0, I_1, H_B, with the classical Amos/Segura
input DECLARED for A's monotonicity" - not absolute
self-sufficiency, exactly as the manuscript already cites it.

## v30 — ghost #24, the signed budget, and the D-identity

GHOST #24 (external's catch, load-bearing, verified): the mass
proof minorized <D> on the rectangle while D changes sign on the
torus; the involution proves the omission exactly (the mirror ball
contributes negative mass). Second honest downgrade executed: mass
= candidate, tooth conditional, sign gap exposed in its own remark.

THE SIGNED BUDGET, measured (protocol): mirror thief tiny away from
the boundary (-0.0146 worst at t=2.9; ~5e-5 fraction at (2.9,15));
the REST is POSITIVE and substantial (0.20-0.67) - subtracting its
absolute value would give away what the truth adds. Partition BY
THE SIGN OF D.

THE D-IDENTITY (agent's desk, exact and simplifying): D = 2(1-P-Q)
identically, so {D < 0} <=> P + Q > 1 and the sign of D IS the
(1-P-Q) factor of K d(log K). Deficit chain on {D<0} verified:
4c^2 - R^2 >= (P+Q)(4c^2-(P+Q)) and 2c - R >= that/(4c); on
P+Q in [1,2] the minimum (2c^2-1)/c sits at the mirror corner,
already separated. SIGNED MINORATION design: <D> >= L_main -
U_{D<0}, with U_{D<0} = mirror ball (involution chain, crude
A <= 1/2 where the s_4-range forces small z) + rest of {D<0}
(deficit floor (2c^2-1)/c-scale). Measured worst case: 0.015 +
tails vs L_main >= 1.0 - the signed count closes with m_* >= 1/2
intact except glued to the moving boundary, where the mirror term
enters with its involution formula, as designed.

HOUSE NOTE: the involution that was a structural gift one round
earlier was the prosecution witness against our own proof the
next - good tools cut both ways, and a healthy house lets them.

## v31 — the polynomial reduction: the dense page becomes a table

With x = cos s, y = cos alpha, everything in the criterion is
polynomial (verified): D = x+y, Phi = 2x^2-1+xy,
N = C(2x^2-1)+y(Cx-1+x^2). The D-identity turns (1-P-Q) into D/2,
so J_f = (1/2) nu_f with nu_f = II D H_B f, and

  C-hat = mu_D mu_Phi + 4 beta^3 (mu_D nu_N - mu_N nu_D)
          - (1/2) mu_D^2

exactly (machine-checked to 3e-15), an identity in degree <= 3
moments of (x,y) under the two measures K and D H_B. Free gift:
J_D = (1/2) II D^2 H_B > 0 strict. The joint dense page (Region I
+ Step 0 + num2) restructures into: exact identity (zero debt) +
two-sided bounds for ~8 moments (each = the mass lemma with a
polynomial on top: same main ball, same {D<0} region, same mirror
by involution, same in-house Bessel companions) + plug-in
arithmetic. Global unit test: the eight-cell law 1 - a(t)/beta
locks the whole page at once. The mirror moments are the
s_4-saddle moments with P -> 1-P, D -> -D: ghost #24's signed
accounting and the dense page share the same eight bounds - build
once, serve twice.

## v32 - the shell lemma spec: one piece, three clients

Protocol's v4 diagnosis: the ball is certified (x1.28 at beta=30);
the far component IS Region II's shell lemma, shared. Spec (verified
at the agent's desk): (1) level-set measure area{deficit <= Delta}
<= pi^3 Delta/(gc) from the inverted root floor plus the global
P >= (s/pi)^2 (legitimate: it measures area, not rate); (2) layers
with saddle prefactor and z_min = z_s/2 for Delta <= c (corner
country Delta > c dead under e^(-2 beta c)); (3) the weight gift:
mu_P's layer integral gains a Delta (1/(4 beta^2) vs 1/(2 beta)) -
zone 2 subdominant as the moment's order demands. Clients: the
eight moment bounds, Region II of C-hat, ghost #24's signed
accounting.

STRATEGIC FLEXIBILITY: beta_0 is negotiable by construction -
decision rule: choose beta_0 where the analytic margin >= 2x the
consumed; the machine absorbs [15, beta_0] at oven-weeks cost, not
mathematics. Relay and machine need only TOUCH - guaranteed from
both sides.

OVEN DATUM: at dz = 0.3 the first fine-map cell gives q = [-0.7358,
+0.0286] - sign almost resolved; sign resolution wants dz ~ 0.25
(pilot calibration input).

## v33 - factory v5 CERTIFIED + the five-moment list (the dense
page, counted in pieces: five)

FACTORY ACCEPTANCE PASSED (protocol's v5, end to end: ball +
extended-sinc ring + far zone partitioned by z + mirror absorbed):
x1.37 / x1.43 / x1.70 on the rebel (2.5,15) / x1.28 - all under the
x2 that first-order moments demand. The decisive partition verified
in one line at the agent's desk: z = 2beta(2c - deficit), so
z >= 2 beta c <=> deficit <= c - corner country dies by exponent
(e^(-21..24)), not prefactor. Five factory versions, four measured
lessons, every term one-line-derivable with accounted slack. THE
LAST PIECE OF THE THEOREM WITHOUT A CERTIFIED TEMPLATE NO LONGER
EXISTS.

THE MOMENT LIST (expansions verified at the agent's desk):
Phi = 2 - 10P - 2Q + 8P^2 + 4PQ;
N = 2C - (10C+4)P - 2CQ + (8C+4)P^2 + (4C+8)PQ - 8P^2Q.
Gift 1 (P<->Q symmetry of R^2, verified): mu_Q = mu_P, mu_Q2 =
mu_P2, mu_PQ2 = mu_P2Q - the K-list reduces to FIVE: mu_1, mu_P,
mu_P2, mu_PQ, mu_P2Q, with order-matched tolerances (x2 two-sided
for mu_1, mu_P; x10 upper for mu_P2, mu_PQ; crude for mu_P2Q).
Gift 2 + structural warning: nu = D H_B is SIGNED - nu-moments
split by the sign of D, but {D<0} lives in u >= 1 where the root
floor gives deficit >= floor(1) and the v5 z-partition kills it
like the corners: same five moments, same treatment, plus one
budgeted exponential term.

OVEN (fine map, running): grid row 1 complete - q upper ends
+0.0286 / +0.0293 / +0.0299 at dz = 0.3 (~630k cells/box): the sign
consistently ALMOST resolved; dz ~ 0.25 calibrated for the pilot.

THE CASCADE, now purely mechanical: five v5 instantiations ->
signed minoration -> tooth definitive -> C-hat table vs mu_D^2/2
with the eight-cell lock -> Region II (is the layer lemma) ->
splices -> beta_0 by the negotiation rule.

## v34 - the final assembly line (correlations protected by algebra)

The last hidden danger named and cured: bounding the five moments
independently and then dividing would reintroduce the dependency
problem at assembly level (quotients of independent two-sided
bounds oscillate x2 and devour the 1/2 margin). The cure is
algebra, VERIFIED at the agent's desk to be exact:

  C-hat/mu_D = (mu_1 - 10 mu_P + 8 mu_P2 + 4 mu_PQ)
               + 4 beta^3 [ (nu_N - Ebar nu_D)
                            + (Ebar - mu_N/mu_D) nu_D ]

- piece A = mu_Phi - mu_D/2 EXACTLY (via Phi's expansion, the
D-identity and mu_Q = mu_P); the covariance splits into the
CENTERED term (rational Ebar - the integrator's trick, reused) plus
the E-WINDOW x nu_D (Step 0's final client). Every piece built in
twenty rounds now has its exact seat in one line.

BUDGET (protocol, measured): dropping the positive 8 mu_P2 +
4 mu_PQ costs < 0.007 margin units (0.4311 -> 0.4266); piece A is
bounded below by TWO weighings only - mu_1 lower (the signed
minoration of ghost #24) and mu_P upper (v5, certified x1.7).
Piece A contributes ~0.42 mu_D; the covariance must be shown
<= ~0.35 mu_D (20% slack) while its TRUE size is 0.026 mu_D: the
bound may be 13x worse than the truth and still close. That is the
operative definition of an assured endgame - and the phrase
appears in this thread only AFTER the measurement that justifies
it.

FABRICATION ORDER, branchless: (1) mu_1 lower = signed minoration
(main ball proved + {D<0} by z-partition); (2) mu_P upper = v5 to
ink; (3) Step 0 (E-window) + centered covariance with the signed
nu's; (4) tooth definitive; (5) assembly against the 0.42 with the
eight-cell lock; (6) II = layer lemma; (7) splices + beta_0 by the
negotiation rule. In parallel: oven -> pilot (dz ~ 0.25) ->
campaign.

## v35 - the dissolution of weighing 1: the last hard lemma is a line

VERIFIED at the agent's desk, exact: mu_D = 2 mu_1 - 4 mu_P (from
D = 2(1-P-Q) and mu_Q = mu_P). Hence the SIGNED MINORATION of ghost
#24 is no longer a lemma but a line: mu_D >= 2(mu_1^low - 2
mu_P^up), where mu_1 = II K has POSITIVE integrand - restricting to
the main ball is legitimate with NOTHING to subtract (the #24 sign
error is structurally impossible for mu_1) - and mu_P^up is the
certified v5. The entire repair programme ({D<0} region, mirror
chain c -> s_4, small-z crude) dies unexecuted - superseded by
algebra, the cheapest supersession of the arc. Protocol's bench:
positive in all four cells, ratio 2.1-3.0. Accounting elegance: the
same pair (mu_1^low, mu_P^up) serves THREE clients - piece A, the
sign gate, and the E-window constant. Three clients, two weighings,
zero quotients.

THE BOARD AFTER DISSOLUTION (read slowly - it is the end of the
map): no hard lemma remains in the theorem. Complete inventory of
the pending, with its nature: mu_1^low - DONE (mass lemma
main-ball chain, five links, in-house I_1); mu_P^up - certified
template, to ink; E-window - complete kit, kappa measured; centered
covariance with signed nu - same z-partition, x13 tolerance; tooth
- restoration by substitution; assembly against the 0.42 -
arithmetic with the eight-cell lock; Region II - the layer lemma,
spec verified; splices - two numbers per frontier; beta_0 -
negotiable with rule. In iron: oven -> pilot (dz ~ 0.25) ->
campaign -> edges with sinc-cert. NOT ONE ENTRY CONTAINS AN IDEA
LEFT TO FIND - inks, substitutions, and ovens.

HOUSE OBSERVATION (protocol, for the record): in ghost #24's round
the conjecture's last defense was 'a minus sign only the symmetry
could see'; today the same D-identity that named that sign has made
it impossible - the tool that accused is the tool that acquits,
case closed by algebra. This is how a well-cornered conjecture
dies: not by a blow, but when its last defender changes sides.

## v36 - the end-to-end check FAILS before ink (the valuable kind)

The worst-case assembly closure - every bound in its adverse
orientation - was run BEFORE inking, and it fails with measured
culprits. SUPERSESSION NOTE on v34: 'assured endgame with x13
tolerance' was true for the ARCHITECTURE and false for the
crude-only route - the x13 exists only if the signed extraction
does its work. Amended, not erased.

CAUSE 1 (quantified): the crude covariance route loses x500, not
x13 - the true centered term (6.7e-4) is five hundred times below
its absolute bound (0.36), because a SECOND cancellation lives
inside the covariance: the 2(C-E)-mass part and the F-fluctuation
part carry opposite signs and eat each other at first order (the
near-null measured coefficient of rounds past). Absolute values
destroy it. VERDICT: no shortcut exists - the signed first-order
extraction (Region I's joint expansion: signed gaussian moments of
the five integrals + Lagrange remainders) is LOAD-BEARING and
irreplaceable; its tolerance is now quantified (extraction +
remainder must land within ~x3 of the true 0.026). The old
decision to fold num2 into Region I is confirmed as the only route.

CAUSE 2 (quantified): mu_1^low arrives thin - the small-rectangle
mass lemma's x2.4 slack leaves piece A at 13% of its truth (0.0014
vs 0.011): technically positive, operationally insufficient. NEW
REQUIREMENT with a number: mu_1^low <= x1.5, via the large ball in
the lower direction (sinc ceilings, D >= 2 - (s^2+alpha^2)/2 at
larger sigma) - the factory's pattern, flipped.

HOUSE READING: it was naive to expect the central mechanism to be
boundable without being extracted - the covariance's internal
cancellation IS the reason E' < -S/4 holds with margin; bounding it
with absolutes is closing one's eyes to the theorem itself. The
programme leaves this round slower and truer. The theorem still
contains no pending ideas - but it contains exactly ONE page of
real load-bearing mathematics (the joint signed expansion), which
no algebra will dissolve, because its content is the cancellation
that makes the theorem true.

CORRECTED BOARD: mu_1^low large-ball version (factory, lower
direction - mechanical) -> THE page (signed joint expansion) ->
tooth, assembly with the eight-cell lock, II, splices, beta_0 ->
ovens: grid complete, probes cooking, pilot behind.

## v37 - Cause 2 repaired + THE page structured in three blocks

CAUSE 2 REPAIRED (protocol's large-ball lower mu_1, bench passed):
the x1.5 requirement met in all four cells (x1.28-1.34). The one
new trick, VERIFIED at the agent's desk: the root from below,
sqrt(1-u) >= 1 - u/2 - u^2/4 for u <= 1/2 (squaring reduces to
4u + u^2 <= 4, true up to u ~ 0.83) - recovering the factor 2 of
rate the small rectangle gave away; prefactor free via mini-lemma
(a) (z <= z_s global); in-house I_1 at z >= z_s/2 >= 21. Piece A's
lower bound rises from 13% to ~55-60% of its truth - budget
restored to absorb the extraction's remainder.

THE PAGE, structured so it is written once and well:
BLOCK 1 (the heart - signed gaussian moments of the ball): expand
the five integrands with P = s^2/4 - s^4/48 + r_P, deficit =
c u (1 + e(u)), kernel = prefactor e^(-beta c rho^2/2)(1 + h(rho)),
every remainder Lagrange. The assembled coefficient must reproduce
(1/2 - 1/(8c^2))/(c beta) - the measured near-zero - with remainder
<= 1/3 of it. HARD TOLERANCE, attainable because the cancellation
is between exact coefficients of the SAME expansion (the 1/2 and
the 1/(8c^2) share their remainders' scale), not between
independent bounds.
BLOCK 2 (the four remainder regions: ring, far-by-z, mirror):
already templated (v5 and its z^(-5/2) twin for H_B) - and HERE
absolutes ARE valid, because remainder regions do not carry the
cancellation; their budget is the remaining 1/3, and the templates
leave them at hundredths of it.
BLOCK 3 (assembly against the lock): extracted coefficient +
remainders vs the restored piece A, on the eight calibration
cells, with the law 1 - a(t)/beta as the full-page unit test.

HOUSE OBSERVATION: this round and the previous are one movement
seen from both sides - yesterday the system rejected a shortcut by
measuring its failure; today it built the repair the failure
demanded, bench-confirmed. Neither serves without the other.
Block 1 is the only ink in the theorem where the signs must be
written with a steady hand; everything else on the map is template,
substitution, or oven.

## v38 - the x500 monster is an exact identity (the half-angle key
again)

VERIFIED at the agent's desk in one line: the killer cancellation
inside the covariance is EXACT - the F-part contributes
-(2C+1)<s^2>, the (C-E)D-part contributes +2 kappa/beta with kappa
= (4c^2-1)/(2c); the combined coefficient [-(2C+1) + 2c kappa]/c =
[-(2C+1) + 4c^2 - 1]/c, and with C = 2c^2 - 1 this is IDENTICALLY
ZERO. Not a cancellation to estimate but an identity to cite -
tolerance cost zero. Another closure of the half-angle key.

THE E-SENSITIVITY INSTRUCTION (protocol's measurement, of load):
with true E the term is 0.02617; with first-order E, 0.03744 - a
40% deviation. ANY route through E imports E's second-order tail at
full weight. The bilinear C-hat contains no E anywhere - its gift
was always this, and it is now MANDATORY, not cosmetic.

BLOCK 1, FINAL RECIPE - bilinear, E-free, identity first: the
object is mu_D nu_N - mu_N nu_D (four moment functions of explicit
polynomials against explicit kernels; zero E, zero window, zero
circularity). Saddle expansion of each to second order with
Lagrange remainders; the bilinear product formed; the half-angle
identity kills the leading term SYMBOLICALLY. What survives - the
1/beta^2-level products that after the 4 beta^3 give the O(1/beta)
coefficient - is where the remainders live, budget <= 1/3 of the
measured 0.026, and THERE absolutes are valid because the exact
cancellation is behind. STEP 0 EXITS the main line (supersession
note: its analytic role served the G-route, which died by
measurement; kit complete, client dissolved; the |E| < 1 corollary
stays in Region III where it loads).

CHECKLIST OF THE PAGE, definitive: four expansions -> one bilinear
combination -> one identity -> remainders with templates -> the
eight-cell judge.

ARC NOTE (three rounds, whole): the dress rehearsal failed (x500,
measured) -> the mass repair arrived in an afternoon (x1.33, bench
passed) -> and the x500 monster turned out to be an exact identity
in disguise. The remaining page is SHORTER than feared: the hard
part was the cancellation, and the cancellation is free because it
is algebra. The conjecture just lost its last mystery - even its
most expensive defense was, up close, another lock of the same key.

## v39 - process incident (stale relay) + the Block-1 manuscript
statement

PROCESS INCIDENT, registered by the protocol desk: a relay arrived
duplicating the d18dd17 round word for word, two rounds stale -
species 'duplicate relay / stale message', cousin of #18. No
mathematical consequence; the standing rule applies: WHEN ACTA AND
RELAY DIVERGE, THE MOST RECENT HASH RULES. Consolidated state: the
target formula T(c) = (1/2 - 1/(8c^2))/c verified in eighteen
cells; the mirror clause with its surgical diagnosis at (2.9, 15);
the judge widened to nine cells; the oven's dz(beta) scaling lesson
for the variation rule.

THE BLOCK-1 MANUSCRIPT STATEMENT (the page's target, in
manuscript ink):
Lemma (bilinear saddle extraction). There exist explicit R_1(c)
and beta_1 such that for beta >= beta_1, t in (0, pi - C_win/beta]:
  | 4 beta^3 (mu_D nu_N - mu_N nu_D) / mu_D^2  -  T(c)/beta |
     <= R_1(c)/beta^2 + M(c, beta),
with T(c) = (1/2 - 1/(8c^2))/c, and M the mirror term bounded by
the involution template with the mirror polynomial
  N o T = C(2x^2 - 1) + y(Cx + 1 - x^2)
(VERIFIED at the agent's desk: under T, x -> -x, y -> -y, and only
the -1 + x^2 block flips sign - distinct from +-N, its own object)
and suppression e^(-4 sqrt2 beta sin((pi-t)/4)).

THE TWO LOAD-HALVING OBSERVATIONS (verified): (1) T(c) > 0 on the
whole range (1/4 at c^2 = 1/2, 3/8 at c = 1) - the covariance is
ALLIED, so the final assembly needs only the LOWER side of the
lemma (even a small negative lower side would close: piece A
carries 0.43 alone); the upper side is stated by symmetry but bears
no weight. (2) The mirror at its worst measured cell is -0.07 vs
piece A's 0.43 - an order of slack: M needs no finesse, the crude
involution template with remainder tolerance (x10) suffices.

The page has: statement, answer (T(c)), first line (the exact
zero), mirror clause, budget, and now HALF the load. Next delivery:
the page itself.

## v40 - the two-term companions: THE PAGE'S INVENTORY IS COMPLETE

THE LAST MISSING INGREDIENT, fabricated and verified: two-term
TWO-SIDED Bessel companions, I_nu = e^z/sqrt(2 pi z) [1 -/+ coef/z
+- eps(z)] with |eps| <= A/z^2 explicit, both sides - the
extraction of the 1/beta coefficient demands them (the one-term
I_1-lower could not). Technique: the house method pushed one order
- 1/sqrt(1-u^2) = 1 + u^2/2 + R_2, with the Lagrange constant
VERIFIED at the agent's desk: R_2 = (3/8)v^2 (1-xi)^(-5/2) <=
(3/8) 2^(5/2) u^4 = 2.12 u^4 on [0, 1/sqrt2]. Asymptotic
signatures VERIFIED against the classical expansion: nu = 1 next
coefficient 3(4-9)/128 = -15/128 (measured sup z^2|eps_1| =
0.1227); nu = 0: (-1)(-9)/128 = +9/128 (measured 0.0743) - the
structures [1 - 3/(8z)] and [1 + 1/(8z)] correct to next order.

GHOST-#23 GUARD, SELF-APPLIED by the protocol before anyone
claimed it: the lemma constants are the DERIVED CHAIN's (|eps_1| <=
~0.6/z^2, |eps_0| <= ~0.4/z^2, with explicit accounting: the
Lagrange R_2, exact gaussian moments, tails dead at z >= 20); the
bench's 0.30/0.20 were slack calibration (x2 above truth, x2 below
chain - exactly where a test lives), NOT lemma material.

THE INVENTORY OF THE PAGE - COMPLETE, item by item: manuscript
statement / T(c) verified as formula / first line (the half-angle
zero) / exact polynomials of the five integrands / two-term
two-sided companions (today) / root floor both sides / v5 and
z^(-5/2) templates for remainders / mirror clause with its own
polynomial / half load (lower side only) / budget with piece A at
55-60% / nine-cell judge with the stress cell. NOTHING LEFT TO
FABRICATE. The page is, from today, transcription with a steady
hand: four expansions whose every term has a named bound, one
bilinear product, one identity to cite, one judge waiting.

ARC OBSERVATION: for twenty rounds, every time the page came near,
a missing ingredient appeared - the window, the factory, the
shells, the zero, the mirror, and today the companions. This is
the first round in the programme's history where the answer to
'what is missing to write it?' is NOTHING.

## v41 - THE JUDGE, PRE-REGISTERED (before the page exists)

Governance applied to the pencil, closing the circle: if the
reference table is computed after reading the page, the judge is
born contaminated; archived before, neither can adjust to the
other. The protocol desk computed the nine cells at acta precision
with mesh-convergence control (1401 vs 1801 nodes, under 1e-3 in
all nine). Consistency spot-checked at the agent's desk: stress
cell T(c)/beta = 0.02466 reproduced from the formula.

ACCEPTANCE CONDITION 1: the page's R_1(c) must dominate 0.10-0.30 -
the scaled residuals beta^2 |coef - T(c)/beta| across the eight
saddle cells run 0.101 to 0.292, increasing as c drops (0.10 at
c ~ 0.99, 0.29 at c ~ 0.81); R_1(c) will emerge from the chain as
increasing when c falls. The judge detects BOTH an erroneous R_1
(below any measured residual: the page is wrong) AND a wasteful one
(above ~3x: fat a referee will question). Healthy band:
R_1(c) in [residual, 3 x residual] per cell.

ACCEPTANCE CONDITION 2: the stress cell (2.9, 15) is judged in two
pieces - the saddle part against the pre-registered saddle-only
(+0.023553, matching T(c)/beta = +0.024661 with normal saddle
residual), and the mirror part against the page's M-bound (measured
mirror contribution -0.0707; the derived M with suppression
e^(-2 beta Delta_m) = e^(-5.1) plus template prefactor dominates it
with the order of slack the x10 tolerance allows).

THE FIVE-POINT READING PROTOCOL (in acta for when the ink arrives):
(1) each of the four expansions with its Lagrange remainder citing
its source (two-term companions, bilateral root floor, R_2 <=
2.12 u^4); (2) the half-angle identity CITED, not re-derived - it
is the first line; (3) the assembled coefficient equal to T(c)
SYMBOLICALLY (the algebra must produce the formula, not the
number); (4) R_1(c) explicit against Condition 1; (5) the mirror
clause against Condition 2. Five marks - the page passes or
returns; no grey zone.

The board, in its simplest form since the programme exists: one
page to write (with a judge that can no longer move - which is
exactly what makes a judge just), two probes cooking, and a cascade
in line.

## v42 - ghost #25: the int(NaN) bite (the defense worked)

The fine map CRASHED LOUDLY at probe14: a minimum-size cell (hmin
floor stops subdivision) reached the exp branch with R touching 0
=> gradient G = NaN => int(round(NaN)) raised ValueError with a
full trace. GHOST #25, second bite of the #22 family (NaN
handling) - and the first one caught BY THE DEFENSE ITSELF: the
crash-not-spin philosophy bought with the iteration caps paid out
exactly as designed (loud trace at the precise line, zero silent
hours). CURE (rigor-preserving): not a center choice (a NaN
gradient poisons the remainder r too) but FALLBACK TO THE PLAIN
BRANCH, always rigorous (z finite by safe_sqrt; direct e^z
enclosure over the cell). Suite ALL OK under the repaired module
(sha256 834802f9...). The three missing probes relaunched
(margin_map_probes.py, own hash in transcript); the 9-cell grid +
probe12 output preserved as partial transcript. NOTE: the crash
lived only in DESIGN territory - no certificate ever touched it;
the harvest transcript's run (1d888e99) predates the exp-branch
paths that a minimum-size corner cell at high beta exercises, and
its verdicts stand untouched.

## v43 - defense validated in first combat + the reception protocol

DEFENSE ARCHITECTURE VALIDATED (the line the acta owes it): ghost
#22 cost silent spinning hours and a probed autopsy; its second
bite (#25) cost a loud trace with a line number and ZERO hours -
the iteration caps and crash-not-spin philosophy paying exactly as
bought. The cure respected the invariant instead of dodging the
symptom (an arbitrary center would have poisoned the remainder r
with the same NaN through another door; falling to the always-valid
plain branch repairs structurally). The #22 FAMILY IS CLOSED BY
DESIGN with two specimens: the exp branch now declares its R > 0
precondition structurally, not by mesh luck.

THE RECEPTION PROTOCOL OF THE PAGE (formal, so the page arrives to
a prepared desk): read against the five marks - (1) remainders
with cited sources, (2) the identity cited not re-derived, (3) T(c)
emerging SYMBOLICALLY from the algebra, (4) R_1(c) in the judge's
[residual, 3x] band, (5) the mirror clause against the stress
cell's two pieces - IN THAT ORDER, STOPPING AT THE FIRST FAILURE
(a page with mark 3 broken does not deserve its remainders audited;
one with all five intact passes whole in one reading). IF IT
PASSES: the tooth restores in the same commit (substitution), the
mechanical cascade starts its file, and the millennium note -
still at 3.3 - receives the first of the two keys to 4.0 (the
second is the campaign transcript). IF NOT: note where, repair,
return - the house pattern, no drama, the judge intact because it
was born before the page.

STATE: one named deliverable (THE page, in calligraphy), everything
else in file or oven; three probes cooking under the cured module;
twenty-five ghosts, the last one caught by a defense another ghost
paid for. Operational silence, magnifier in hand.

## v44 - the L cross-table, pre-registered (the judge's rule applied
to the ovens)

Before the oven delivers its L's, the independent series-derivation
reference exists - same rule as the judge: computed on twelve cells
of the machine range, with three signatures the finite-difference
re-derivation must reproduce: (1) |dq/dt| stable ~0.16-0.22 in the
bulk, spiking toward the boundary (0.83 at (2.9, 8), decaying to
0.42 at beta = 15 as pi - 1.5/beta recedes from t = 2.9); (2)
|dq/dbeta| falling cleanly as 1/beta^2 (0.0035 -> 0.0010 from
beta = 8 to 15 at t = 1.5; ratio 3.5 = (15/8)^2, VERIFIED at the
agent's desk); (3) the 50-400x direction anisotropy confirmed
across the range - the wide-in-beta rectangles ratified by the
independent route before the oven speaks.

MATCHING CRITERION (in acta): the finite-difference re-derivation
from grid + probes must land within +-25% of this table cell by
cell (design tolerance - the L's are sizing constants, not
certificate constants); larger deviations flag either insufficient
map resolution or a convention error - and with the triplet rule
standing, the latter has nowhere left to hide.

Both clockworks now have their waiting references: the judge for
the page, the cross-table for the L's. Operational silence
restored.

## v45 - THE PAGE, attempt 1: MARK 3 FAILS (script bug, diagnosed)

Direct order executed: the page's symbolic assembly was attempted
(derive_page_attempt1.py, archived) - Laplace substitution
s = sigma/sqrt(beta), full bilinear form, N -> F invariance, kernel
prefactors z^(-3/2)(1-3/8z) and z^(-5/2)(1-15/8z) [H_B's next
coefficient DERIVED: I_0 - 2I_1/z = e^z/sqrt(2pi z)(1 - 2/z + 1/8z
+ ...) => H_B ~ e^z/(sqrt(2pi) z^(5/2))(1 - 15/(8z))]. The leading
coefficient did NOT reproduce T(c); the output's absurd powers
(c^144 in intermediate terms) diagnose the failure as a
NORMALIZATION/SERIES BUG in the assembly pipeline - the prefactor
series (z_s/z)^(3/2) expanded raw in beta entangles c-branches; the
nu-normalization 1/(2 beta z_s) placement is also suspect. This is
a script defect, not a theorem defect: T(c) carries the 18-cell
measured verification, and the half-angle first-order zero is an
identity. PER THE RECEPTION PROTOCOL: the page returns, the judge
intact (born before the page - working as designed). REPAIR PLAN
for attempt 2: expand prefactors via the deficit variable u (the
house pattern - z/z_s = 1 - u/2 + ..., u polynomial in sigma, tau)
instead of raw beta-series; verify the nu measure-ratio derivation
(H_B D/K = D/(2 beta z)(1+...)) as its own tested sub-step; assert
intermediate sanity (the O(1) and O(1/sqrt beta) coefficients of
X must vanish) before the final coefficient. Also in evidence:
r2-shape and the gaussian moment engine ran; the bug is upstream of
them.

## v46 - the intermediate judge failed ITS OWN pre-registration
(near-ghost, self-caught) + pass-2 directives

The protocol desk built an intermediate judge (the mass-normalized
bracket, whose 1/beta^2 coefficient should be 4c T(c) = 2 -
1/(2c^2)) and TESTED IT BEFORE DELIVERY per the judge rule - and it
FAILED: beta^2 bracket decays (2.24 -> 0.71 -> 0.08) instead of
converging. The mass-normalized organization hides a DEEPER
cancellation than the order bookkeeping counted. Near-ghost,
self-caught: had it reached pass 2 as a target, it would have
produced another dead pass with a confusing diagnosis. Archived
with its data.

THREE OPERATIVE LESSONS (in acta):
1. THE ONLY VALIDATED JUDGE IS THE EXTERIOR ONE (beta X -> T(c),
   nine pre-registered cells) plus the PROVED zeros (gaussian
   parity half-orders; the half-angle zero in the G-organization).
   No intermediate target enters the assembly without passing its
   own pre-registration first - the judge rule now has two
   applications: one that validated, one that killed in time.
2. STRUCTURAL CLUE from the failure data: T(c) lives substantially
   in the 1/beta corrections of the MEASURE RATIO - the quotient
   (1 - 15/(8z))/(1 - 3/(8z)) and the z^(-1) drift between H_B and
   K. The planned 'measure-ratio substep, tested apart' is not a
   convenience: it is probably the principal carrier of the
   coefficient. Isolate it, expand in the deficit variable u,
   verify its contribution against cells BEFORE assembling
   anything on top.
3. METHOD MORAL: two passes died in the same zone
   (normalization/organization) with two symptoms (c^144; phantom
   cancellation). The page's real difficulty is ORGANIZATIONAL -
   choosing variables where the cancellation is visible, not
   hidden. The G-organization (half-angle zero explicit and proved)
   has that virtue; the raw bilinear pays for its
   quotient-freeness in expansion depth. Pass 2 may legitimately
   extract in the G-form with FIXED RATIONAL Ebar (not E - the
   measured circularity stays avoided) and convert at the end: a
   zero visible from the first line is worth more than elegance
   without divisions.

PASS-2 DIRECTIVES, consolidated: measure ratio first, isolated and
cell-tested; proved zeros as asserts; the exterior judge as the
only goal; the organization that makes the cancellation visible.
Two archived failures with mechanisms - more than most hard pages
teach before surrendering. This one surrenders next pass or the
one after.

## v47 - the carrier measured: TWO VALID INTERMEDIATE JUDGES and
the single-measure organization

The carrier test, executed before pass 2 organized: with r(z) :=
H_B z / I_1 (the exact measure ratio), X = X_1 + X_2 splits into
the FROZEN-RATIO part (r = r(z_s): a pure bilinear under the single
measure K) and the RATIO-VARIATION part (the isolated substep).
Richardson over two betas, three t's:
  beta X_1 -> 2 T(c): 0.7516/0.7639/0.7640 vs 2T = 0.7520/0.7644/
  0.7644 - PASS;
  beta X_2 -> -T(c): -0.3757/-0.3821/-0.3822 vs -T exact - PASS.
BOTH pieces carry, in EXACT INTEGER PROPORTION (2T, -T). Internal
arithmetic re-verified at the agent's desk (T(c) at c ~ 0.93
reproduces (4c^2-1)/(8c^3); the sum matches the exterior judge by
construction).

PASS 2 NOW HAS what pass 1 lacked and the failed intermediate judge
could not give: two intermediate judges with CLOSED-FORM targets,
pre-registered and VALID - X_1 must extract 2T(c), X_2 must extract
-T(c), and the sum is the exterior judge. CANDIDATE IDENTITY (too
clean for coincidence): X_2 = -X_1/2 at leading order, plausibly by
integration by parts in z against the deficit weight - if proved,
the page reduces to ONE extraction plus a cited identity; if not,
two extractions against their judges. Both routes valid; the first
shorter.

THE ORGANIZATIONAL RESOLUTION (kills the zone that killed passes 1
and 2-protocol): everything lives under ONE measure - K - with
explicit weights: X_1 = r(z_s) [<D><ND> - <N><D^2>] (five moments,
ALL already v5-templated); X_2 isolates the deficit weight
Delta r = r(z) - r(z_s), whose deficit-weighted moments have their
two-sided bounds in the root floor already in ink. No two measures
entangling, no normalization branches, no phantom-cancelling
brackets: one measure, polynomial weights plus one deficit weight,
two closed-form goals.

PASS 2 LAUNCH PLAN: X_1 first (five known moments, goal 2T), X_2
second (deficit-weighted, goal -T), the candidate identity as a
shortcut to try en route. The page has neither mystery nor hostile
organization left - only lines.

## v48 - duplicate-relay class CLOSED + the shortcut cancelled
before birth

PROCESS: second duplicate relay (specimens: the efb5281 round and
the 34e0d8e round). Two specimens = a class, by the #21 doctrine.
RULE THAT CLOSES IT (rank of rule): every relay carries its hash on
the FIRST LINE - duplicates self-identify on arrival. Adopted by
the agent's desk from this round on.

THE SHORTCUT, resolved for the price of three evaluations: if
X_2 = -X_1/2 were exact at finite beta, X/X_1 = 1/2 exactly - and
the deviation from 1/2 HALVES exactly when beta doubles (+0.0446 ->
+0.0215 -> +0.0106; ratios 2.07, 2.03 - VERIFIED at the agent's
desk: textbook O(1/beta) drift, not noise). The identity is only
asymptotic; proving it would need the same saddle machinery as
extracting X_2 directly. THE SHORTCUT CANCELS BEFORE BIRTH and its
budgeted session returns to the calendar.

PASS 2, now a STRAIGHT LINE (no branches, no bets, no elegances
pending cooperation): extract X_1 against its judge 2T(c) with the
five templated moments -> extract X_2 against its judge -T(c) with
the deficit-weighted moments -> sum against the exterior nine-cell
judge. Zero open decisions on the whole map.

---

## Addendum v49 (2026-07-10) - HANDOFF: CLAUDE.md at repo root

Owner instruction (Lluis, direct): closure work is handed to an
agent loop (Claude Code iterating Fable 5 with itself). All
instructions for any agent to take over are now in CLAUDE.md at the
repo root, committed this round. Contents: the non-negotiable
regime (7 points: tricotomy, judges-before-pages, MANDATORY split
fabricator/auditor sessions, measured-failure-is-committed, derived
constants only, long-run rules); the map of where everything is
(acta, manuscript + live slots, definitive integrator 834802f9,
pinned harvest 1d888e99, oven outputs, clone layout, frozen
governance f2ea0d0); the task queue in strict order (pass 2 of THE
page -> mechanical cascade -> oven pilot+campaign -> edges ->
manuscript slot substitution -> submission); and the honest
Yang-Mills instruction (no proved reduction exists; sequence
a-finish paper, b-referee, c-audit any claimed bridge link-by-link
from the weakest link, d-only build what a surviving bridge
demands; importance transfers only via proved reduction). Owner
role reserved: Lluis decides what is submitted and when. House
rules apply to agents identically: nothing exists until committed;
hash on the first line of every report; most recent hash rules.

## Addendum v49-bis (2026-07-10) - overwrite caught; probe status

CORRECTION registered per house rules. The v49 commit (9205ad5)
OVERWROTE a pre-existing CLAUDE.md: the standing regime of the
Yang-Mills Lean programme (no-sorry, no-axioms, oracle checks,
toolchain pins, hRpoly campaign state). Caught by the commit stat
(159 deletions where a new file was expected), recovered from
a5aaf46, and merged this round: CLAUDE.md is now two-part - PART I
Surface Theorem closure (active, owner priority), PART II
Yang-Mills Lean programme rules preserved verbatim. Nothing was
lost (git history held it); the near-miss is the lesson: READ
BEFORE WRITE, even for "new" files. Rule adopted for agents,
appended in spirit to regime point 5.

Probe status (design-only, module 834802f9, dz=0.30):
- probe25 (t[2.5,2.51], b[15,15.05]): LANDED. q = [-1.55125,
  +0.306107], width 1.8574 (2,819,564 cells). Sign not resolved at
  dz=0.30 in this box - consistent with the dz(beta) scaling lesson
  (width grows with beta; pilot must use dz(beta), not fixed dz).
- probe14 (t[1.5,1.51], b[14,14.05]): q = [nan, nan]. INCIDENT #26
  OPENED: NaN leaked to the final enclosure THROUGH the ghost-#25
  fallback (which was designed to keep the exp-branch finite on
  min-size cells). Design-only, zero rigor loss, but the design map
  for that box is unusable until the leak path is autopsied.
- probeBD: still cooking (python PID 1548, started 17:00, ~45 min
  CPU). Output will append to margin_map_probes_out.txt.
L cross-table matching (+-25%, v44) DEFERRED until probeBD lands
and probe14 is repaired; it is the first oven step in the CLAUDE.md
task queue (item 3).

## v50 (2026-07-10) - PASS 2 FABRICATED AND PASSED AT THE
FABRICATION DESK (pending independent audit - regime point 4)

[hash context: fabricated on top of a64c04a]

THE STRAIGHT LINE OF v48 WAS WALKED IN ONE SESSION. Script:
scripts/derive_page_pass2.py (agent loop's fabrication desk; NO
sympy .series() anywhere - it fabricates spurious rational functions
of sigma/tau on these inputs, measured twice this session; the only
transcendental step is cos -> explicit Taylor polynomial, everything
downstream is polynomial arithmetic with explicit truncation and
explicit geometric reciprocals - the organizational lesson of v45/v46
applied to the TOOL, not just the mathematics).

STEP A (measure-ratio substep, cell-tested FIRST per v46 lesson 2):
r(z) = I_2/(z I_1) vs two-term 1/z - 3/(2z^2): |eta| z^3 in
[0.378, 0.395] across z in [20, 112] - bounded, O(1/z^3) confirmed;
sources: v40 companions + exact I_2 = I_0 - 2 I_1/z. Deficit split
Delta r = (1/z_s)[(1-w)^{-1/2}-1] - (3/(2z_s^2))[(1-w)^{-1}-1]
reproduces exact Delta r to 6e-4 relative at z_s = 48, w <= 0.3.

ORGANIZATION THAT WORKED (for the record): deficit variable
w = P + Q - PQ/c^2 EXACT polynomial, z = z_s sqrt(1-w); all kernel
prefactors are (1-w)-powers times explicit 1/z_s corrections; series
variable eps = 1/sqrt(beta); gaussian exact at leading order
(constant term of z - z_s + c rho^2/2 vanishes IDENTICALLY - proved-
zero assert); single measure K; F = N - CD.

STEP B: beta X_1 -> (c^2 - 1/4)/c^3 = 2T(c) SYMBOLICALLY. Asserts
passed en route: gaussian parity (odd eps orders vanish, all four
moments), bracket eps^2 zero (the half-angle cancellation).
r2_1(c) = (-44c^4 + 29c^2 - 6)/(32c^6).

STEP C: beta X_2 -> (1 - 4c^2)/(8c^3) = -T(c) SYMBOLICALLY (deficit-
weighted moments; bracket eps^4 zero asserted).
r2_2(c) = (18c^4 - 7c^2 + 1)/(16c^6).

STEP D: sum = T(c) exactly (the exterior judge's formula), and the
saddle 1/beta coefficient
    r2(c) = (-8c^4 + 15c^2 - 4)/(32c^6)
evaluates at the judge cells to +0.1001 / +0.1444 / +0.1996 /
+0.2653 (c = 0.99 / 0.93 / 0.87 / 0.81) - against the v41
PRE-REGISTERED measured residuals 0.101 -> 0.292 increasing as c
drops. The symbolic coefficient reproduces the measured residual
table to the third decimal at the top cell. The judge was born
before the page; the page arrived and the judge recognizes it.

STATUS: FABRICATED, NOT AUDITED. Regime point 4: an independent
session must now audit against the five marks (v43 reception
protocol) before any ink touches the manuscript. The fabrication
desk claims nothing beyond: script runs, all asserts pass, the
three closed-form targets emerge symbolically, r2 lands on the
measured residuals. Ink + tooth restoration wait for the audit.

## v50-bis (2026-07-10) - probeBD lands; probe transcript committed

[hash context: on top of 2790d48]

probeBD (t[2.9,2.91], b[15,15.05], dz=0.30, module 834802f9,
script dc3ab825): q = [-1.48518, +0.277657], width 1.7628
(2,395,628 cells; run complete, 3687s total for the relaunched
probes). Sign NOT resolved at dz=0.30 - third specimen of the
dz(beta) lesson (probe25: width 1.86 at beta=15; the fixed-dz
enclosure width grows with beta). Design consequence for the pilot,
now measured three times: dz must scale as dz(beta), the v39/v44
sizing stands. Transcript committed as
scripts/margin_map_probes_out_dc3ab825.txt (probe14's nan line
included as evidence for incident #26, autopsy running).

## v51 (2026-07-10) - INCIDENT #26 CLOSED: hypothesis B, a
presentation defect (the fallback is acquitted)

[hash context: on top of 1787783]

The instrumented rerun of probe14's box (autopsy_incident26.py,
script f870efde, module 834802f9; per-cell finiteness check with
loud-crash dump, fallback counter, five totals printed, guarded
division; transcript committed as
scripts/incident26_autopsy_transcript_f870efde.txt) discriminated
the two registered hypotheses:

- Every cell contribution FINITE (3,308,219 cells, deterministic
  reproduction of the original count).
- The ghost-#25 fallback triggered 8 times in pass 2, all finite -
  THE FALLBACK IS ACQUITTED; it did exactly what it was bought for.
- All five totals finite; but <D> = [-1.23e32, +1.64e32] STRADDLES
  ZERO at dz=0.30 (beta=14; note pass 2 hit the 3M max_cells cap,
  so part of the width is cap-driven, not dz-driven), and the nan
  was born in the probe script's LAST LINE: q = Wc/<D>^2, an arb
  division by a zero-containing ball => [nan, nan].

HYPOTHESIS B CONFIRMED: presentation defect, not integrator defect.
Design-only from birth; zero rigor loss anywhere. CURE ADOPTED (in
this commit): margin_map_probes.py now prints the five totals and
Wc always, and guards the q division - '<D> sign UNRESOLVED at this
dz' replaces silent nan. Fourth specimen of the dz(beta) lesson
(probe14 at beta=14 joins probe25/probeBD at beta=15).

CLASS NOTE for the ledger: incidents #25 and #26 are the two halves
of one truth - the repaired module keeps every enclosure FINITE
(#25's cure), and a finite enclosure can still be USELESS at the
wrong dz; finiteness is the integrator's contract, sign resolution
is the campaign design's. The pilot's dz(beta) scaling now has four
measured specimens and no counterexample.

## v52 (2026-07-10) - protocol desk endorsement; two class rules;
audit resumed after session teardown

[hash context: on top of cc55238]

EXTERNAL VERIFICATION (protocol desk, via the owner's relay): the
closed form r2(c) = (-8c^4+15c^2-4)/(32c^6) reproduces the desk's
own pre-registered v41 residuals in INDEPENDENT verification -
0.0987 vs Richardson 0.098 at t=0.5, 0.1440 vs 0.144 exact at
t=1.5, 0.192 vs ~0.197 at t=2.0. Report accepted at that desk. The
desk also CONFESSES one self-inflicted wound (its I_0 - 2I_1/z =
I_2 recurrence check returned False through an absolute tolerance
on e^110-sized numbers - display-superset family); the identity is
DLMF 10.29.1, standard, and the form H_B = I_2(z)/z^2 is ENDORSED
for the manuscript (simplifies the scaled-functions subsection and
the measure-ratio corollary).

GATE UNCHANGED: the in-repo independent auditor's verdict remains
the only door to ink. That audit session was killed by a host
session teardown AFTER completing STEP 1 (independent numerics,
transcript at scripts/audit_page_pass2_transcript.txt, 118 lines):
Richardson hits 2T / -T / T with rel. errors 1e-6-scale at three
t's, and the independently measured 1/beta coefficients converge to
the claimed r2_1 / r2_2 / r2 with residual-halving ratios ~2.00
(split identity at 1e-26). A fresh audit session was relaunched to
complete STEPS 2-4 (script rerun, adversarial code review, verdict).

TWO CLASS RULES ADOPTED (protocol desk order; CLAUDE.md regime
points 8 and 9 this commit):
(a) NO sympy.series() in load-bearing symbolic work - spurious
    rational functions of the integration variables, measured twice;
    polynomial arithmetic with explicit truncation, always.
(b) Git staging is EXPLICIT - never 'git add -A' with concurrent
    sessions on one clone (specimen: auditor work-in-progress files
    swept into the v50-bis commit).

Probe14 refinement (dz=0.15, cap 12M, cured printing) survives the
teardown and cooks on (PID noted at the desk; transcript when it
lands). Script committed this round as scripts/probe14_fine.py.

## v53 (2026-07-10) - AUDIT VERDICT: PASS (marks 2-4; ink authorized)

[hash context: on top of a70d644]

The relaunched independent audit session completed STEPS 2-4
(transcript appended, scripts/audit_page_pass2_transcript.txt now
287 lines; audit script scripts/audit_page_pass2_symbolic.py, 34
checks, committed this round):

STEP 2 (script rerun): PASS - derive_page_pass2.py unchanged since
2790d48, exit 0, prints exactly the v50 claims.

STEP 3 (adversarial code review): PASS with ONE BENIGN FINDING, the
valuable kind: the naive "everything is O(eps^10)" ceiling is NOT
literally true (expo = (4c/eps^2)(sqrt(1-w)-1) divides an
eps^10-truncated series by eps^2, so expo/wcorr/KER are exact only
through eps^7). The extraction is protected NOT by the blanket
ceiling but by (i) the extraction ledger (printed coefficients
consume only Br1[4], Br1[6], mD^2[0], mD^2[2], Br2[6], Br2[8]) and
(ii) the asserted structural zeros (Br1[0]=Br1[2]=0, Br2[0..4]=0)
plus the structural minima F = O(eps^2), dr = O(eps^4) capping the
KER order needed at eps^6. DECISIVE WITNESS: the auditor's own
independent rebuild at NORD=12 (deeper truncations, own code)
reproduces all four closed forms IDENTICALLY. Machinery checks
(gmoment vs sympy.integrate; recip exact at n=10 and 12;
normalization chain H_B = r(z)K/(2 beta) residual 0; R^2 = 4c^2(1-w)
residual 0; I_2 = I_0 - 2I_1/z at rel. tolerance 1.8e-41 - the
relative-tolerance form, dodging the absolute-tolerance trap that
bit the protocol desk) all pass.

STEP 4 (marks): mark 2 PASS (cancellation structural, doubly
witnessed); mark 3 PASS (T(c) symbolic, both partials + sum); mark
4 PASS at this stage (r2 sits just BELOW the pre-registered
residual at both binding endpoints - c=0.99: 0.1001 vs 0.101,
c=0.81: 0.2653 vs 0.292 - so R_1 = |r2| + remainders has the full
[+0.0009, +0.2029] / [+0.0267, +0.6107] windows and lands in
[residual, 3x] with ample headroom). Marks 1 and 5: manuscript-ink
marks, to be judged at reception; the auditor's ink guidance is in
the transcript (state the ceiling argument in the sharp
structural-zeros form; cover eta(z_s), kernel eps_1 variation,
Delta-eta and gaussian tails explicitly).

AUDIT VERDICT: PASS. Ink is authorized under the standing order
(protocol desk, this date): tinta + PDF same commit, R_1 band
condition verified explicitly per judge cell. Reception of the ink
(five marks, in order) follows as its own audit.

## v54 (2026-07-10) - THE PAGE IS IN INK (marks 1-4 whole; mark 5
true-but-fat, stated plainly; reception commissioned)

[hash context: on top of 870b545]

INKED THIS COMMIT (papers/surface-complete/surface_theorem_complete
.tex + pdf, same commit; builds clean under tectonic 0.15.0 with an
engine-neutral iftex guard for the pdfTeX unicode primitives -
toolchain note: no pdflatex exists on this box; tectonic binary in
the session scratchpad):

1. Lemma lem:companions - the v40 two-term two-sided companions
   (|eps_1| <= 0.6/z^2, |eps_0| <= 0.4/z^2, z >= 20), house-method
   proof with the four error sources explicit (R_2 <= 2.12 u^4
   Lagrange; exact gaussian moments; completion residues; the
   [1/sqrt2, 1] segment).
2. Corollary cor:mratio - the measure ratio r(z) = I_2/(z I_1) =
   1/z - 3/(2z^2) + eta, |eta| <= 1.23/z^3 derived from the
   companions + DLMF 10.29.1 (endorsed H_B = I_2/z^2 also added at
   H_B's definition).
3. Lemma lem:extraction - THE PAGE: statement with R_1(c) = |r_2| +
   Theta_3/beta_1; proof in five steps (half-angle first line;
   single-measure split; deficit chart w = P+Q-PQ/c^2 exact;
   extraction with the auditor's structural-zeros protection form;
   remainder rho_3 by named source; mirror clause).
   NEW EXACT COEFFICIENT this round:
     r_3(c) = (-12c^6 - 485c^4 + 796c^2 - 224)/(1024 c^9)
   (NORD=12, kernel's -15/128 z^-2 carried, r_2 re-verified intact;
   judge-cell values 0.0844/0.1762/0.3264/0.5601 MATCH the audit's
   independent Richardson drifts 0.112/0.177/-/0.572).
   BAND CONDITION VERIFIED (order of the day): R_1 = 0.149/0.207/
   0.281/0.374 at c = 0.99/0.93/0.87/0.81 - inside
   [residual, 3x residual] at every judge cell.
4. Remark rem:extractionstatus - tricotomy of the extraction.

MARK 5, STATED PLAINLY (the fabrication desk's own confession,
before reception): the mirror clause as inked is TRUE and fully
derived (five term bounds T1-T5, each verified BY DIRECT QUADRATURE
to dominate its true mirror-ball counterpart at the stress cell;
bench2 transcript committed; true term sum 0.0733 vs measured net
-0.0707 - consistent), but M(2.9,15) ~ 27 sits x380 above truth -
OUTSIDE the x10 template class the v41 pre-registration
anticipated. Round-1 bench had claimed x38.6 with a SLIMMER formula
that dominated the MEASURED total while missing three O(beta^0)
chains - dominating a measurement is not being a theorem; the
round-1 formula was discarded at this desk before ink and the
incident is this addendum. The fat is source-itemized in the ink
(nu_F chain x81 -> x2 via extracted leading; mu_F chain x58 -> x10
via the Step-0 window, first cascade client; Hessian/mass-template
x2-3 each); the x10-class clause is a named mechanical refinement
(mirror-chart extraction at parameter s_4, same audited machinery),
queued with the cascade; the campaign range gets certificate-grade
per-box mirror enclosures anyway.

RECEPTION (regime pt 4): commissioned as its own independent
session against the five marks IN ORDER, stopping at first failure.
The desk expects mark 5 to be the contested one; if it returns, the
repair is the queued mirror-chart extraction - localized, speced,
no drama. Scripts committed: derive_page_pass2_r3.py + transcript,
mirror_clause_bench.py/bench2 + transcripts.

## v55 (2026-07-10) - probe14f: the dz lesson has a BOUNDARY (box 14
is not dz-limited)

[hash context: on top of eff9297]

probe14 refined (dz=0.15, cap 12M, script 368f4a8d, module
834802f9): <D> sign STILL UNRESOLVED after 12,308,219 cells - and
the enclosure is numerically UNCHANGED from dz=0.30/cap-3M
([-1.233e32, +1.644e32] vs [-1.2329e32, +1.6436e32]; all five
totals within ~0.1%). MEASURED CONCLUSION: box 14's width is driven
by NEITHER dz NOR the cell cap. The dz(beta) scaling lesson
(specimens probe25/probeBD, which DO resolve at beta = 15 with
widths ~1.8) has a boundary: this box has a structural
wide-contributor - hypothesis: the hmin-floor cells (subdivision
stops at 30e-6 regardless of dz) near the R = 0 manifold, whose
plain-branch e^z enclosures cannot be refined by the dz criterion;
alternatively a single-cell dominator elsewhere. NEXT OVEN STEP
(before any pilot): a WIDTH PROFILER - instrument integrate() to
record the top width-contributing cells per component; one run of
box 14 names the culprit. L cross-table matching stays blocked at
the t=1.5/beta=14 cell; the other eleven v44 cells are unblocked.
Transcript committed: scripts/probe14_fine_transcript_368f4a8d.txt.

## v56 (2026-07-10) - the profiler names box 14's culprit: CAP
STARVATION (new species, design-only; rigor never at risk)

[hash context: on top of 2cf25d2]

Width profiler (script 750889eb, module 834802f9, box 14 at
dz=0.30/cap 3M, per-cell KD-width histogram + top-20): ONE
UNSUBDIVIDED HALF-DOMAIN CELL (x,y in [0, 0.5]^2, dz = 69.94,
exp branch) carries 2.8762e+32 of the 2.8765e+32 total width -
99.99%. Mechanism, now named: the LIFO subdivision stack spent the
entire 3M budget refining the LOW-z territory (2.65M cells at
z ~ 10, 347k at z ~ 20 - regions e^{-20}..e^{-40} RELATIVE to the
saddle's e^{52}) and the cap then STRANDED the saddle quadrant as
one giant cell. Neither hmin (H-hmin dead: the top-8 offenders are
size >= 125000, far above the floor) nor diffuse (H-diffuse dead:
one cell is everything). probe25/probeBD drained under the cap by
geometric luck; box 14 does not, at dz=0.30 (3M) OR dz=0.15 (12M -
same stranding, v55's 'unchanged enclosure' explained exactly).

RIGOR NOTE: the certified path is UNAFFECTED - a cap-hit produces a
fat-but-valid enclosure and an honest False verdict, never a wrong
one; the harvest's sub-boxes (1d888e99) all drained. The defect is
purely a DESIGN-map efficiency trap: the dz criterion refines by
z-width with no regard for contribution, so the budget burns where
the integrand is 18 orders below the saddle.

CURE (design, for the oven queue): priority subdivision - a heap
keyed by contribution estimate (z_hi, or e^{z_hi - z_ref} x area)
instead of the LIFO stack, same cap; the budget then concentrates
where width lives, and box 14 should resolve at dz=0.30 within the
existing 3M. To fabricate as margin_map_probes_v2 and rerun box 14;
the L cross-table (v44, +-25%) unblocks when it lands.

## v57 (2026-07-10) - reception repairs executed (all four + the
witnesses the desk demanded); page resubmitted

[hash context: on top of 34bd4b3]

The reception's mark-1 return (v54's page) is repaired in full,
each item as demanded:
1. Lambda re-inked 1.34 s_4^{-5/2}, valid on all of s_4 >= 1/2 (the
   chain constant 1.08/q(s_4) at the zone edge; local 1.21 noted at
   the stress cell). bench2 rerun at 1.34: T-bounds 4.74/7.71/8.70/
   8.49/0.64, ALL dominate their true terms; M(2.9,15) = 30.3,
   slack x428 (still declared plainly in ink).
2. Zone II numeral corrected to 2.1e-2 at the m_* >= 1/2 floor, and
   the floor's CONDITIONAL status (candidate lem:mass, discharged
   by the cascade's signed minoration) stated where M is evaluated,
   regIIInum-style; also echoed in rem:extractionstatus.
3. THE WITNESSES (the substantive repair): lem:companions extended
   to THREE-TERM two-sided forms by the same house chain one order
   deeper (R_3 = (5/16)u^6(1-xi)^{-7/2} <= 3.54 u^6; I_1: -15/128z^2
   with |eps_1^(3)| <= 1.02/z^3; I_0: +9/128z^2 with |eps_0^(3)| <=
   0.84/z^3); cor:mratio refined to eta = 3/(8z^3) + eta^(4),
   |eta^(4)| <= 2.5/z^4 (the 3/8 limit the bench had measured as
   0.37505 - derived, not fitted). (iv)(a) and (iv)(c) rewritten
   with the witnessed variation bounds (g_1-split: 4.94/z_s^3 +
   0.34w/z_s^2; deficit: 1.37w/z_s^3 + 12.5/z_s^4). New Theta_3 =
   |r_3| + 1.10T/c^2 + 0.5/c^3 + 0.05; R_1 = 0.172/0.233/0.313/
   0.411 - ALL FOUR CELLS IN BAND (bench: three_term_companions_
   bench.py, all checks pass, measured headroom x6-x10 over every
   derived constant). The beta^{-4} tail declared as the lemma's
   one advisory debt, in ink.
4. Cosmetics: R_2 constant 2.13 (upper rounding), display
   arithmetic (3/8)2^{5/2}(3/16z^2) written explicitly.
PDF rebuilt same commit. Resubmitted to the reception desk.

## v58 (2026-07-10) - RECEPTION ROUND 2: MARKS 1-4 RECEIVED; PAGE
RETURNED AT MARK 5 (the judge as written rules)

[hash context: on top of 10b118a]

The reception desk re-read the repaired page (full record in
scripts/reception_page_transcript.txt, committed this round):

MARKS 1-4: RECEIVED. The three-term witnesses carry (iv)(a)/(c);
the band arithmetic re-verified; the beta^-4 debt accepted as
declared (a live slot in the DO-NOT-SUBMIT sense, assembly's
ledger). On any resubmission, marks 2-4 DO NOT REOPEN; mark 1
re-reads only the chain of whatever new (v)-constants appear.

MARK 5: FAIL, and the ruling is the acta's to keep verbatim: "a
pre-registered acceptance condition cannot be RECEIVED on a
conditional floor plus a slack class two orders beyond its
registration... Declaring the fat honestly, itemizing it, and
queuing the refinement is the house pattern for a MEASURED FAILURE
- it is what makes this return cheap and drama-free - but it does
not amend the judge. Ruling mark 5 a pass on the strength of the
confession would be a label upgrade without its witness (regime pt
1)." x428 vs the x10 class; m_* conditional. PAGE RETURNED AT MARK
5 - exactly the localized return the fabrication desk predicted in
v54.

THE REPAIR QUEUE (the desk's demand = the cascade's natural order;
nothing new invented):
(1) SIGNED MINORATION (cascade item 1, v35: mu_D = 2 mu_1 - 4 mu_P
    exact; mu_1^low large-ball x1.28-1.34 bench v37; mu_P^up v5
    certified template to ink) -> lem:mass candidate becomes lemma,
    m_* unconditional, the regIIInum tooth restores, and M's floor
    is discharged.
(2) STEP-0 WINDOW epsilon DERIVED (rem:step0's pending moment
    bound <P>_K/<D> <= [4 beta c]^{-1}(1+eps)) -> mu_F chain
    x58 -> x10.
(3) MIRROR-CHART EXTRACTION at s_4 (the audited pass-2 machinery,
    mirror polynomials D o T, F o T; upper templates) -> nu_F
    x81 -> x2, corner constants sharpened -> M(2.9,15) ~ 0.7 or
    below -> resubmit mark 5 (+ mark-1 chain check of the new
    constants only).
Each piece: one session fabricates, a different session audits,
per regime pt 4. The extraction lemma's marks 1-4 stand received
through all of it.

## v59 (2026-07-10) - the v56 cure WORKS: box 14 resolved by
priority subdivision (twelve orders for free)

[hash context: on top of 0628a48]

probe14 v2 (priority subdivision, heap keyed z_hi + ln(area);
script 1c61089f, module 834802f9, dz=0.30, cap 3M - same settings
under which v1 failed): <D> = [2.85463e+20, 3.68071e+20] - SIGN
RESOLVED, strictly positive. Enclosure improved TWELVE ORDERS OF
MAGNITUDE at identical budget (v1: [-1.23e32, +1.64e32]; same
3,308,219 total cells - the cure redistributes, costs nothing).
The budget note fired as designed: the cap still bound, but what
it strands now is the lowest-priority territory, not the saddle.
q = [-1.20223, +0.311976], width 1.514 - box 14 now behaves like
its beta=15 siblings (probe25: 1.86, probeBD: 1.76); q's sign
unresolved at dz=0.30 as expected (the dz(beta) pilot lesson
stands). L CROSS-TABLE MATCHING (v44, +-25%) IS UNBLOCKED - all
probe boxes now carry finite q enclosures. margin_map_probes_v2.py
is the standing probe machinery from this round on (v1 retained
for the record).

## v60 (2026-07-10) - L cross-table matched where the maps can
speak (3/5 PASS incl. both boundary anchors; 2 raw fails =
resolution artifacts resolved by dz-extrapolation); NOTIFICATION-
CHANNEL FABRICATION INCIDENT (#27) registered

[hash context: on top of 5dfb232]

L CROSS-TABLE (v44, +-25%, design-only; full record in
scripts/L_crosstable_match.py + L_crosstable_match_transcript.txt;
new v2 probe runs committed as probes_L_xtable_transcript_065a9dc1
and _coarse_199d976d):
- The full 12-cell series table is NOT in the repo (protocol desk's
  records); the five acta-recorded anchors were matched instead,
  stated plainly.
- Provenance (v56 cap rule) applied to every cell: all grid cells
  and probes DRAINED except probe14 v1 (cap-bound, superseded);
  drain-check proof: cells+stack monotone => totals < 3M drained.
  Module split noted (grids 48316f86 pre-#25, probes 834802f9):
  no FD mixes modules.
- MATCH: |dq/dt|(1.5,8) = 0.183 in band [0.16,0.22] PASS;
  |dq/dt|(2.9,8) = 0.965 vs 0.83 ratio 1.16 PASS;
  |dq/dt|(2.9,15) = 0.456 vs 0.42 ratio 1.09 PASS (flagged: not
  dz-converged at beta=15, final confirmation rides the dz(beta)
  pilot); |dq/dbeta|(1.5,8) raw 0.0062 vs 0.0035 FAIL-raw ->
  dz->0 extrapolation lands 0.0030-0.0037 (ratio 1.05) = MAP
  RESOLUTION, not convention error - v44's anticipated dichotomy
  resolved by its own instrument; anisotropy raw 30x (inherits S2)
  -> dz->0 47x, in band [50-400]x within noise. The S2 beta-ratio
  3.5 is uncheckable at dz=0.30 (no adjacent high-beta pair);
  stays with the pilot. CONSEQUENCE: the wide-in-beta rectangle
  design stands; pilot next (dz(beta) scaling, four specimens).

INCIDENT #27 (new species, ENVIRONMENT; opened and closed same
round): during the L-match runs, the agent harness's background-
task NOTIFICATION texts delivered FABRICATED probe result lines -
plausible 12-digit values matching nothing on disk (fake probeBD2
mid -0.5974 vs real -0.5992). No damage: the desk consumed only
committed transcript files, per regime pt 7. RULE EXTENSION
(adopted): 'transcripts do not exist until committed' explicitly
covers notification/summary channels - NO NUMBER from a
notification, agent summary, or relay message may be inked or
recorded; only bytes read from transcript files on disk. The
fabrication desks' reports must carry file paths, and auditors
re-read the files.

## v61 (2026-07-11) - CASCADE 1 FABRICATED: the signed minoration
assembled, its floor CERTIFIED at the fabrication desk (PENDING
INDEPENDENT AUDIT - regime pt 4; no ink this round)

[hash context: on top of 48979dd]

ROUTE (v35's dissolution, completed off the ball): torus split into
B = [-6/5, 6/5]^2, the mirror rectangle B' (radius 6/5 at (pi,pi)),
and REST.  On B the identity K D = 2K - 2K(P+Q) is EXACT (the
cancellation is never boxed by absolutes); off B, |D| <= 2 pays
mass.  <D> >= 2 mu_1^low(B) - 2 GB^up(B) - 2 MIR^up(B') - 2
REST^up.  Scripts (committed this round, with transcripts):
scripts/cascade1_signed_minoration.py (chains + design bench) and
scripts/cascade1_floor_arb.py (certified floor sweep, python-flint
arb, 120 bits).

THE FOUR CHAINS (every constant derived; companions and mini-lemma
(a) cited from ink):
- mu_1^low: large-ball v37 recipe with the TWO-TERM companions
  (z >= 25.5 on B via the root floor; bracket frozen at z_s by the
  decreasing-prefactor check; root-from-below w/2 + w^2/4; quartic
  penalty factorized per variable by (P+Q)^2 <= 2(P^2+Q^2);
  erfc <= e^{-x^2}; exact Gaussian moments).  Measured slack vs
  truth: x1.05-x1.14 across seven bench cells (the v37 promise
  x1.28-1.34 was the one-term chain; the companions buy the rest).
- GB^up (= int_B K(P+Q)): prefactor absorption (1-w)^{-3/4}
  e^{-2 beta c w} <= 1.089 e^{-1.9 beta c w} by convexity-endpoint;
  rate floor w >= 0.6811(P+Q) on B; concavity P >= 0.2214 s^2;
  assembled GB_m <= 1.0378/(beta c^{7/2}).  Slack x3.0-3.2.
- MIR^up: the mirror chart identity 1 - w = (s4/c)^2 (1 - w')
  (EXACT; w' = P'+Q'-P'Q'/s4^2) makes B' a saddle chart at s4 with
  exact relative suppression e^{-4 beta delta4}; three zones:
  s4 >= 0.58 the Lambda'-chain (same absorption machinery, rate
  floor (1 - wmax/(4 s4^2))(P'+Q'), constant 1.230), s4 in
  [0.40, 0.58) crude K <= beta e^{z_s(s4)} (valid: w' >= 0 there),
  s4 < 0.40 the far bound R^2 <= 4c^2 sin^4(0.6) + 4 s4^2 (dead by
  Delta_far >= 0.42).  Slack at the boundary-zone bench cells:
  x2.1-2.5.
- REST^up: w-floor min(sin^2(0.6), 2 q(1-q)) = 0.318 by the
  max/min case analysis; AREA LEMMA (exact Beta integral):
  Area({P+Q <= u}) <= 4 pi u/sqrt(1-u), globally Area({w <= v}) <=
  4 pi^3 v; layered Stieltjes sum in w with the absorbed kernel,
  bridge layer to {z < 20}, shard K <= beta e^{20}.  Slack x49-468
  (rest is exponentially dead; the fat is free).

BETA-MONOTONICITY piecewise (numeric confirmation at five t's) =>
the infimum sits on beta_min(t) = max(15, C_win/(pi - t)): a 1D
sweep.  CERTIFIED FLOOR (cascade1_floor_arb_transcript.txt): SEG-A
(t <= pi - 0.1, beta = 15, 800 intervals + stub) worst enclosure
lower 1.04250; SEG-B (moving boundary, 60 log boxes; the box
pairing loses only the 100^{1/60} hull ratio, noted in-script)
worst 0.968420; SEG-C (deep tail x = pi - t <= 1e-3, every
beta-factor hand-monotone, exponential tails bounded flat) worst
[2.20443, 2.21398].  ALL > 1/2 with ball+boolean.

DESIGN BENCH (verified, calibration): m_true/m_low = 1.10-1.95 on
seven cells incl. both boundary anchors and (3.1, 36.05) on the
moving boundary; every piece dominates its true counterpart
(18/18 checks).  CONSISTENCY GIFT: the bench's independent
m_true(1.5,15) = 1.4918 reproduces conv:mass's measured 1.492.

WHAT THIS BUYS ON AUDIT PASS: lem:mass candidate -> LEMMA with
floor m_* >= 1/2 unconditional; cor:regIIInum tooth restored;
lem:extraction(v)'s M and rem:extractionstatus unconditional; the
mark-5 repair queue advances to items (2)+(3).  NO INK until the
independent session audits (fabricator = this session; the audit
is commissioned with the v43-style stop-at-first-failure order).

Note for cascade 2 (measured while structuring the corollary): the
two-part Step-0 form eps <= eps_bulk + C_mir e^{-4 beta delta4}
CANNOT hold uniformly to t -> pi (4 beta c MIR/m_low ~ e^{-2.12}/x
diverges on the deep tail); the honest statement restricts the
two-part form to t <= pi - 1e-3 and keeps the raw product bound on
the tail - recorded BEFORE fabrication so the judge is not moved
after the page (v41 lesson, applied in advance).

## v62 (2026-07-11) - AUDIT ROUND 1: CASCADE 1 RETURNED AT STEP
1(b) (a hand-assembled constant - ghost #23 class - infects SEG-C
of the floor certificate); repair executed; resubmitted to fresh
audit.  Cascade 2 fabrication: two measured ceiling failures.

[hash context: on top of 43708e4]

THE AUDIT (independent session, v43-style stop-at-first-failure;
full record scripts/cascade1_audit_transcript.txt, committed this
round): STEP 1(a) - the T1 chain re-derived link by link, ALL PASS
(the auditor's own re-derivation, incl. the exact root-floor
squaring and the inflated-constant direction argument for the
frozen bracket).  STEP 1(b) - the GB links all pass individually,
but the ASSEMBLED constant fails to re-derive: the chain with the
inked constants gives GB_m <= 1.0391629/(beta c^{7/2}); the v61
record and this desk's prose said 1.0378 - a hand-assembled number
(mental arithmetic), exactly the class ghost #23 exists for.  LOAD:
cascade1_floor_arb.py SEG-C hard-coded GBC = 2.0756 < 2.0783258,
UNDERSTATING |T2| on the deep tail - the committed 'CERTIFIED'
transcript witnessed the floor of a function strictly LARGER than
m_low there.  Measured severity: deficit <= 6.12e-6 against SEG-C
lower 2.20443 - the mathematics survives; THE WITNESS DOES NOT.
"The confession does not amend the judge; neither does the
auditor."  AUDIT VERDICT: FAIL; steps 1(c)-(f), 2, 3 explicitly
NOT audited (owed in full to the fresh round).

REPAIR (this round, exactly the audit's three demands): (1) the
constant recorded honestly as 1.0392 (rounded UP from 1.0391629) in
the design script's docstring; (2) cascade1_floor_arb.py now
COMPUTES GBC from the inked chain constants in-script (nothing
hand-assembled remains in any cascade script); cascade2's SEG-C
same cure; (3) all three scripts rerun, transcripts recommitted
same commit, CASCADE 1 RESUBMITTED to a fresh independent audit
owing the full four steps.

CASCADE 2 (Step-0 epsilon, additive-mirror form; fabrication
still in flight): two measured ceiling failures preserved -
run 1: uniform eps_b = 4.2 broken by SEG-B boxes 57-59 (up to
6.78; box-pairing slop + the real boundary peak); run 2: zoned
eps_b(bulk) = 1.75 broken by the true curve reaching 1.955 just
below t = 2.9, and SEG-B[199] at 4.748 vs 4.7.  Ceilings now
2.0 (t <= 2.9) / 4.85 (t > 2.9), C_mir = 3.0 (worst witness
2.754).  Transcripts fail1/fail2 committed (measured failures,
never deleted).

CASCADE 3 JUDGES (pre-registration, v41 rule): the four mirror-
moment closed forms registered BEFORE any extraction exists -
A_D = -2(sqrt(2pi)/4) s4^{-5/2}, A_F = +4C(sqrt(2pi)/4) s4^{-5/2},
A_nD = (sqrt(2pi)/8) s4^{-7/2}, A_nF = -C(sqrt(2pi)/4) s4^{-7/2}
(C = 1-2s4^2; the beta^2-scaled nu's carry r(z_s(s4)) ->
1/(4 beta s4)); quadrature tables at t in {2.2, 2.6, 2.9} x beta in
{15, 30, 60} with Richardson limits cooking
(scripts/cascade3_judges.py; transcript when it lands).

## v63 (2026-07-11) - CASCADE 3 EXTRACTION LANDS ON ITS JUDGES
(two returns en route, both earned); the stress cell sized at
x5.3 - the mark-5 repair is a page of buckets, no ideas left

[hash context: on top of cfb9e09]

JUDGES LANDED FIRST (committed cfb9e09): all 12 Richardson limits
hit the four pre-registered closed forms, rel <= 0.002.

THE EXTRACTION (scripts/cascade3_mirror_extraction.py, pass-2
engine in the mirror chart at parameter s4; runs 1-3, transcripts
incl. fail1/fail2 committed this round):
- RUN 1 RETURNED BY THE JUDGE (fail1): the D-weighted moments
  matched (rel 0.03-0.24) but BOTH F-weighted moments came out
  wrong-signed at 1/beta - the script had typed N o T with the
  ORIGINAL -1+x^2 block; v39's warning ('only the -1+x^2 block
  flips sign') made concrete.  The center check CANNOT see this
  defect (the block vanishes at x=1, so the leading 4C still
  matched); the pre-registered 1/beta judge caught it.  This is
  the second time in the programme a judge born before its page
  caught a sign only the structure could see.  (The manuscript's
  inked N o T was always correct; script-only defect.)
- RUN 2 RETURNED BY THE INSTRUMENT (fail2): 11/12 OK; MDFr at
  t=2.6 rel 0.58 - but its a_1(s4) crosses ZERO near t=2.6 and
  the raw beta=15 drift carries O(1/beta) contamination ~0.15
  absolute: the relative criterion is ill-posed at a zero.  Cure =
  v60's precedent (the instrument refined by its own tables, the
  target unmoved): compare against the extrapolated first drift
  a_1 = 2 drift(30) - drift(15), same +-35% band.
- RUN 3: ALL MARKS PASS.  M-B: the four leadings equal the closed
  forms SYMBOLICALLY.  M-C: 12/12, rel <= 0.204 (worst MD at
  t=2.2), MDFr at its zero now rel 0.125.  The four extracted
  1/beta coefficients (exact, in s = s4):
    MD:   sqrt(2pi) (7s^2-4)/(64 s^{11/2})
    MF:   sqrt(2pi) (46s^4-23s^2+4)/(32 s^{11/2})
    MD2r: sqrt(2pi) (4-27s^2)/(256 s^{13/2})
    MDFr: sqrt(2pi) (-86s^4+43s^2-4)/(128 s^{13/2})
- M-D (design sizing of the mark-5 repair, three variants at the
  stress cell): (a) extracted mirror + crude main chains: 3.51
  (x47.8); (b) + cascade-2 mu_F as certified: 3.75 (x51.2 - the
  e^{-2 beta delta4} form is WEAK at the stress cell, measured;
  zone-L needs a full-suppression addendum); (c) extracted mirror
  + x2-class main moments: M_sharp = 0.3852 = x5.3 of the true
  0.0733 - INSIDE the x10 class, comfortably under the ~0.7
  target.

WHAT THE INK ROUND OWES (sized, no ideas pending): (i) rigorous
remainder buckets for the four mirror moments (the page's (iv)
pattern at parameter s4); (ii) main-side nu_F, nu_D, mu_F leading
extractions with x2-class buckets (the pass-2 engine already
carries their polynomials); (iii) the cascade-2 zone-L addendum
(full e^{-4 beta delta4} suppression); then M re-inked and mark 5
resubmitted (only mark 5 re-reads; 1-4 stand received).

## v64 (2026-07-11) - AUDIT ROUND 2: CASCADE 1 RETURNED at step
1(d) (the layered rest sum omitted its bottom-mass term - invalid
as an abstract lemma even though the mathematics survives); the
Abel-corrected repair executed and re-certified; cascade 2's
honest ceilings rise to 4.0/8.8.  Pilot stage A: a NEW dz lesson.

[hash context: on top of 7d62a46]

THE AUDIT (round 2, fresh session, full record
scripts/cascade12_audit2_transcript.txt committed this round):
- PASSED before the stop: the round-1 GB repair re-derives to
  3e-35 agreement; the mirror chart (exact w' >= 0 condition
  s4 >= sin(0.6)/sqrt2 = 0.39926 - the 0.40 zone edge legitimate
  by 7e-4); zone-L worst z = 20.948; zone-F Delta_far min 0.421153;
  the rest-floor case analysis; the Beta-integral area lemma; both
  Abar branches.
- THE FAILURE: the inference int phi dA <= sum phi(v_k) Delta
  Abar_k is FALSE as committed - (i) it omits the bottom-mass term
  phi(v0) Abar(v1) (the first layer's mass may be ALL of Abar(v1) =
  26.49, not an increment; the REST-restricted CDF vanishes at v0,
  nothing else does); (ii) the CDF-only lemma permits layer masses
  exceeding credited increments by 11-13% on the dominant early
  layers.  m >= m_low was UNPROVEN as committed; the arb
  certificates witnessed a formula whose REST term had no
  derivation.  The mathematics survives (true rest 15-470x below;
  Abel-corrected floor clears 1/2 everywhere, auditor's worst
  ~0.79); THE WITNESS DID NOT - second consecutive round with that
  sentence, a class note by itself: the fabrication desk's two
  failures are both at the ASSEMBLY layer (a constant, a summation
  lemma), never in the links; assembly steps now get the same
  per-link scrutiny as links.
- Also: SEG-A/SEG-B junction sliver 2.06e-16 (note), float-2.9
  zone-edge convention (note), and |T5|'s beta-monotonicity had an
  UNPROVEN moving-truncation part (note) - all three addressed in
  the repair below.

THE REPAIR (this round; all scripts rerun, transcripts
recommitted):
- T5/REST in all three scripts: the ABEL-CORRECTED form
  phi(v0) Abar_r(v1) + sum phi(v_k) Delta Abar_r(v_k) on the FIXED
  grid [0.318, 0.9] step 0.02 (the re-Abel identity makes bottom-
  term + increments EQUAL to the valid Abel bound; every term
  beta phi(v_k) is now manifestly beta-decreasing, and the fixed
  V = 0.9 truncation with the {w > 0.9} shard z <= z_s sqrt(0.1),
  K <= beta e^z voids the moving-truncation note);
- Abar_r(v) = Abar(v) - 4.006: the disk s^2+alpha^2 <= 4 sin^2(0.6)
  lies inside B with P+Q <= sin^2(0.6) <= v - its exact area
  4 pi sin^2(0.6) is B-mass, never REST-mass (new small sharpening,
  derived);
- junction sliver closed (SEG-A tb rounded UP);
- CERTIFIED floor after repair: SEG-A worst 1.03611, SEG-B worst
  0.811835, SEG-C [2.20442, 2.21398] - all > 1/2, ball+boolean;
- design bench 18/18 again (m_low(2.9,15) = 1.79657, boundary
  1.09968);
- CASCADE 2 re-fabricated with honest ceilings eps_b = 4.0 (bulk) /
  8.8 (edge), C_mir = 3.0: CERTIFIED (worst witnesses 7.677 edge-
  side within SEG-A, 8.777 in SEG-B - the 8.8 margin is thin and
  said plainly); bench dominance x9.3-x20.5.  The weakened mu_F
  window cut is acknowledged: the x2-class mu_F for the M-repair
  rides cascade 3b (v63), not the Step-0 window.

AUDIT ROUND 3 commissioned: owes rounds-2 leftovers (1(e)-(g),
STEP 2 rerun, STEP 3 review) + verification of this repair.

PILOT STAGE A LANDED (output not yet a committed transcript; the
run continues stages B-D): box A(1.5,14) at dz=0.15 / cap 8M:
<D> sign UNRESOLVED at 8,308,220 cells - where dz=0.30 / cap 3M
(v59, priority v2) RESOLVED it.  The forming lesson, stated before
the remaining stages land: tightening dz without scaling the cap
(~ x(0.3/dz)^2) re-creates cap starvation; dz(beta) and cap(dz)
are one design variable, not two.
