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
