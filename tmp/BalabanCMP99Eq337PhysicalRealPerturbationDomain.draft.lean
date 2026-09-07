import YangMills.RG.BalabanCMP99Eq337PhysicalRealCovariantDerivative
import YangMills.RG.BalabanCMP99SourceScaledStratification

/-!
PRE-VALIDATION: this scratch source has no materialized `.olean` and no
compiler or axiom-oracle verdict.

# CMP99 (3.37): physical real-slice perturbation domain

The source field `A'` lives on the fine lattice.  Its bounds are imposed on
each fine carrier `Omega_j`; they are not a freely chosen family of fields on
the coarsened lattices.  This module therefore quantifies over the nonterminal
regions of the existing global stratification and keeps the scale
`L^j * eta` literal.

This is only the physical real slice.  The complexified perturbation domain
required by the holomorphic theorem remains a separate producer.
The covariant derivative is fixed to the concrete `matrixSUNAdjointModel`;
the source-facing domain cannot be inhabited using a caller-chosen action.
-/

namespace YangMills.RG

noncomputable section

variable {L N' Nc n : ℕ}
variable [NeZero L] [NeZero N'] [NeZero Nc] [NeZero n]
variable {scaleExtent : Fin n → ℕ}
variable {S : CMP99SourceScaledStratification (FinBox 4 (L * N')) n
  (fun r => FinBox 4 (scaleExtent r))}

/-- Literal physical spacing `L^j eta` in CMP99 (3.37). -/
def cmp99Eq337PhysicalScaleSpacing (L : ℕ) (j : ℕ) (eta : ℝ) : ℝ :=
  (L : ℝ) ^ j * eta

/-- Literal amplitude majorant `alpha1 (L^j eta)^-1` in (3.37). -/
def cmp99Eq337PhysicalAmplitudeMajorant
    (L : ℕ) (j : ℕ) (eta alpha1 : ℝ) : ℝ :=
  alpha1 * (cmp99Eq337PhysicalScaleSpacing L j eta)⁻¹

/-- Literal covariant-derivative majorant
`alpha1 (L^j eta)^-2` in (3.37). -/
def cmp99Eq337PhysicalCovariantDerivativeMajorant
    (L : ℕ) (j : ℕ) (eta alpha1 : ℝ) : ℝ :=
  alpha1 * ((cmp99Eq337PhysicalScaleSpacing L j eta)⁻¹) ^ 2

/-- Physical real-slice membership in the perturbation domain (3.37).

The same fine-lattice one-cochain `A` is restricted to every nonterminal
source region `Omega_j`.  The explicit `[NeZero n]` prevents the entire source
range `j = 0,...,k` from becoming vacuous.  No independent scale-indexed
family is accepted.
-/
structure CMP99Eq337PhysicalRealPerturbationDomain
    (U : PhysicalGaugeBackground 4 (L * N') Nc)
    (A : PhysicalGaugeOneCochain 4 (L * N') Nc)
    (eta alpha1 : ℝ) : Prop where
  eta_pos : 0 < eta
  alpha1_pos : 0 < alpha1
  amplitude_bound : ∀ r : Fin n,
    CMP99PhysicalOneCochainAmplitudeBoundOn
      (S.global.regions r.castSucc) A
      (cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1)
  covariant_derivative_bound : ∀ r : Fin n,
    CMP99Eq337PhysicalRealCovariantDerivativeBoundOn
      (S.global.regions r.castSucc) (matrixSUNAdjointModel Nc) eta U A
      (cmp99Eq337PhysicalCovariantDerivativeMajorant
        L r.val eta alpha1)

/-- The fine spacing cancels from the exponential argument.  Hence the
literal (3.37) amplitude majorant is uniformly controlled by `alpha1` at
every source scale. -/
theorem CMP99Eq337PhysicalRealPerturbationDomain.abs_eta_mul_amplitudeMajorant_le
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {A : PhysicalGaugeOneCochain 4 (L * N') Nc}
    {eta alpha1 : ℝ}
    (D : CMP99Eq337PhysicalRealPerturbationDomain
      (S := S) U A eta alpha1)
    (r : Fin n) :
    |eta| * cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1 ≤
      alpha1 := by
  have hL : (1 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast (NeZero.one_le : 1 ≤ L)
  have hpow : (1 : ℝ) ≤ (L : ℝ) ^ r.val := one_le_pow₀ hL
  have hinv : ((L : ℝ) ^ r.val)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hpow
  have hcancel :
      |eta| * cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1 =
        alpha1 * ((L : ℝ) ^ r.val)⁻¹ := by
    rw [abs_of_pos D.eta_pos]
    unfold cmp99Eq337PhysicalAmplitudeMajorant
      cmp99Eq337PhysicalScaleSpacing
    field_simp [D.eta_pos.ne']
    <;> ring
  calc
    |eta| * cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1 =
        alpha1 * ((L : ℝ) ^ r.val)⁻¹ := hcancel
    _ ≤ alpha1 * 1 := mul_le_mul_of_nonneg_left hinv D.alpha1_pos.le
    _ = alpha1 := by ring

/-- Named specialization of the first literal (3.37) bound at one scale. -/
theorem CMP99Eq337PhysicalRealPerturbationDomain.amplitude_bound_at
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {A : PhysicalGaugeOneCochain 4 (L * N') Nc}
    {eta alpha1 : ℝ}
    (D : CMP99Eq337PhysicalRealPerturbationDomain
      (S := S) U A eta alpha1)
    (r : Fin n) (x : FinBox 4 (L * N'))
    (hx : x ∈ S.global.regions r.castSucc) (nu : Fin 4) :
    ‖A (x, nu)‖ <
      cmp99Eq337PhysicalAmplitudeMajorant L r.val eta alpha1 :=
  D.amplitude_bound r x hx nu

/-- Named specialization of the covariant derivative bound at one scale. -/
theorem CMP99Eq337PhysicalRealPerturbationDomain.covariant_derivative_bound_at
    {U : PhysicalGaugeBackground 4 (L * N') Nc}
    {A : PhysicalGaugeOneCochain 4 (L * N') Nc}
    {eta alpha1 : ℝ}
    (D : CMP99Eq337PhysicalRealPerturbationDomain
      (S := S) U A eta alpha1)
    (r : Fin n) (x : FinBox 4 (L * N'))
    (hx : x ∈ S.global.regions r.castSucc) (mu nu : Fin 4) :
    ‖cmp99Eq337PhysicalRealCovariantDerivative (matrixSUNAdjointModel Nc)
        eta U A
        (x, mu, nu)‖ <
      cmp99Eq337PhysicalCovariantDerivativeMajorant
        L r.val eta alpha1 :=
  D.covariant_derivative_bound r x hx mu nu

end

end YangMills.RG
