# SURFACE-CLOSURE RESEARCH NOTES — session 2026-07-09c
Status: **Conjecture part (i) PROVED (two independent proofs). Part (ii) reformulated;
generic routes adversarially closed; specific route identified.**

## 0. The exact framework discovered (all verified numerically to 30+ digits)

Everything lives on the Dirichlet interval (0,π) inside the circle. Define:

- k1(φ) := e^{β cos φ} (von Mises kernel), Fourier: I_m(β).
- **K2(φ) = Σ_m I_m² e^{imφ} = I₀(2β cos(φ/2))** (classical product identity; verified).
- H(ψ) := −K2′(ψ) = β sin(ψ/2) I₁(2β cos(ψ/2)) ≥ 0 on (0,π), closed form.
- s1(ψ) := Σ_m m I_m sin(mψ) = (β/2) sin ψ e^{β cos ψ} > 0 on (0,π), closed form.
- **Killed one-step kernel**: q1(t,ψ) := k1(t−ψ) − k1(t+ψ)
  = **2 e^{β cos t cos ψ} sinh(β sin t sin ψ) > 0** on (0,π)² (closed form!).
- Operator (Qf)(t) := (1/2π)∫₀^π q1(t,ψ) f(ψ) dψ. **Eigen: Q sin(m·) = I_m(β) sin(m·)**
  (verified). Q is positivity-improving (kernel > 0).
- Two-step kernel: k(t,ψ) := K2(t−ψ) − K2(t+ψ) = 2Σ I_m² sin(mt)sin(mψ); k = q1∘q1;
  eigenvalues I_m².
- The surface objects: F_B(t) = Σ m I_m⁴ sin(mt), F_A(t) = Σ I_m²[(m−1)I_{m−1}²
  + (m+1)I_{m+1}²] sin(mt) (I₁-normalization dropped; W scales positively).
  **Coefficient identities: F_B = Q³ s1** (m I_m⁴ = I_m³·(m I_m));
  **F_A = Q²(H·cos)** up to the same constant as F_B = Q²(H/2)·(2) — the shift
  weights collapse: Σ[(m−1)I_{m−1}²+(m+1)I_{m+1}²] sin(mψ)-coefficients ⟺
  w(ψ) = 2 cos ψ · S(ψ), S = H/2 (verified: both kernel forms match series at
  ratio exactly 1/2, common constant).

## 1. THEOREM (Conjecture (i)): F_B > 0 on (0,π), all β > 0. PROVED.

**Proof (a) — spectral/positivity (one line).** F_B = Q³ s1 with s1 > 0 on (0,π)
and Q positivity-improving (q1 = 2e^{βcc'}sinh(βss') > 0). ∎

**Proof (b) — reflection lemma.** F_B = −½(K2 * K2)′. LEMMA: if g,h are even,
2π-periodic, (strictly) decreasing on (0,π), then g*h is even and (strictly)
decreasing on (0,π). Proof: (g*h)′(φ) = (1/2π)∫₀^π g′(ψ)[h(φ−ψ) − h(φ+ψ)]dψ;
g′ ≤ 0 on (0,π), and h(φ−ψ) ≥ h(φ+ψ) because the circle distance satisfies
|φ−ψ| ≤ min(φ+ψ, 2π−φ−ψ) for φ,ψ ∈ [0,π] (both checks are one line); strict on
positive measure. Apply with g = h = K2 = I₀(2βcos(φ/2)), strictly decreasing
since cos(φ/2) ↓ and I₀ ↑. ∎

Both proofs elementary; (b) is a general lemma of independent interest
(symmetric-decreasing IS preserved by circular convolution).

## 2. Part (ii) reformulated (exact, verified)

F_A(t)/F_B(t) = 2·E_{ω_t}[cos ψ], where dω_t(ψ) = H(ψ)[K2(t−ψ) − K2(t+ψ)]dψ ≥ 0
on (0,π) (bracket ≥ 0 by the distance inequality above). Conjecture (ii)
⟺ t ↦ E_{ω_t}[cos] strictly decreasing
⟺ for every λ ∈ (−1,1): G_λ := Q²[H·(cos−λ)] has at most one sign change
   (+ → −) on (0,π). [H(cos−λ) itself has exactly one, at arccos λ.]

## 3. NEGATIVE results (adversarial; corrects an earlier sampling artifact)

- q1 is NOT TP₂ for β ≳ 3/2: ∂²log q1/∂t∂ψ = βs_ts_ψ + c_tc_ψ·βg(βs_ts_ψ),
  g(z) = coth z − z/sinh²z; negative in the anti-diagonal corners (t≈0, ψ≈π).
  Verified: min ≈ −92 at β=100.
- k = q1∘q1 is NOT SR₂/TP₂ for β ≳ 8: corner (t≈0.08, ψ≈3.06) gives
  ∂²log k/∂t∂ψ ≈ −3.3 (β=20), −17 (β=100). **My earlier "TP₂: 1189 random
  rectangles, 0 violations" was a SAMPLING ARTIFACT** — random boxes miss the
  thin corner. Lesson recorded (ghost-class: random ≠ adversarial testing).
- Consequences: the MLR/variation-diminishing route is CLOSED in generic form
  (SR₂ fails ⟹ Q² does not diminish variation on ALL one-sign-change data).
  Any proof of (ii) must use the SPECIFIC family H·(cos−λ): these vanish like
  sin at the endpoints and carry almost no mass in the SR₂-violating corners
  (H(ψ)→0 as ψ→π like β²(π−ψ)/2·...; the violating region is measure-starved).

## 4. Next-session routes for (ii), in order

(α) λ-family level crossing: show G_λ(t) = F_A − λF_B has ≤ 1 sign change via
    Sturm-type argument: G_λ = Q²[h_λ], h_λ one sign change; track zeros under
    the smoothing Q (Q's kernel q1 > 0 is a strictly positive analytic kernel —
    zeros of Q²h_λ are analytic in λ; boundary behavior computable:
    F_A/F_B(0⁺) = 2E_{ω_0}[cos] and → 2·(−1)+... at π⁻; check whether
    E_{ω_t}[cos] endpoints straddle λ monotonically).
(β) Quantitative corner control: SR₂ holds OUTSIDE corners of size O(1/β)
    (from the Δ formula); mass of ω_t in corners is exponentially small
    (H·k factors) — hybrid argument: MLR on the bulk + explicit corner bound.
    This fits the measured phenomenology (mirror cancellation e^{−2.1β}).
(γ) FKG/two-copy: E_{ω_t}[cos] monotone ⟺ Cov_{ω_t}(cos ψ, ∂_t log k) ≤ 0;
    integrate the corner failure against the H-weights explicitly.

## 5. Numerics reproduction
All identities and negatives above have inline mpmath/sympy checks in the
session transcript; key formulas exact to 30+ digits. Precision warning for W
itself still stands: dps ≥ 2.2β + 20.
