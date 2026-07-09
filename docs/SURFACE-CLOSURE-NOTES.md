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
