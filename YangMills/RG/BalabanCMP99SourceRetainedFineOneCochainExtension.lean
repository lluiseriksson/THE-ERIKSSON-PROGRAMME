import YangMills.RG.BalabanCMP99SourceRetainedFineExtension
import YangMills.RG.BalabanCMP99Eq337PhysicalComplexCovariantDerivative

/-!
# Canonical retained extension of a physical perturbing one-cochain

The real physical perturbation is kept on the exact retained fine read
carrier and set to zero elsewhere.  Complexification is performed only after
this source-closed extension, so the analytic branch cannot receive an
independently chosen complex perturbation.
-/

namespace YangMills.RG

noncomputable section

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
variable {Omega : ActiveGaugeRegion d N}

/-- Zero extension of the physical perturbation outside the exact retained
fine read carrier. -/
noncomputable def CMP99SourceActiveRegionChain.retainedFineOneCochainExtension
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (A : PhysicalGaugeOneCochain d N Nc) :
    PhysicalGaugeOneCochain d N Nc := by
  classical
  exact WithLp.toLp 2 fun b =>
    if b ∈ regions.retainedFineReadBonds (Nc := Nc) then A b else 0

@[simp] theorem CMP99SourceActiveRegionChain.retainedFineOneCochainExtension_apply_of_mem
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d N)
    (hb : b ∈ regions.retainedFineReadBonds (Nc := Nc)) :
    regions.retainedFineOneCochainExtension A b = A b := by
  classical
  simp [CMP99SourceActiveRegionChain.retainedFineOneCochainExtension, hb]

@[simp] theorem CMP99SourceActiveRegionChain.retainedFineOneCochainExtension_apply_of_not_mem
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d N)
    (hb : b ∉ regions.retainedFineReadBonds (Nc := Nc)) :
    regions.retainedFineOneCochainExtension A b = 0 := by
  classical
  simp [CMP99SourceActiveRegionChain.retainedFineOneCochainExtension, hb]

/-- A local pointwise radius becomes a global radius after zero extension. -/
theorem CMP99SourceActiveRegionChain.norm_retainedFineOneCochainExtension_le
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (A : PhysicalGaugeOneCochain d N Nc) (rA : ℝ) (hrA : 0 ≤ rA)
    (hA : ∀ b ∈ regions.retainedFineReadBonds (Nc := Nc), ‖A b‖ ≤ rA) :
    ∀ b, ‖regions.retainedFineOneCochainExtension A b‖ ≤ rA := by
  intro b
  classical
  by_cases hb : b ∈ regions.retainedFineReadBonds (Nc := Nc)
  · rw [regions.retainedFineOneCochainExtension_apply_of_mem A b hb]
    exact hA b hb
  · rw [regions.retainedFineOneCochainExtension_apply_of_not_mem A b hb]
    simpa using hrA

/-- Complexifying the source-closed physical extension is the canonical
analytic perturbing one-cochain.  This definition prevents independent
complex data from entering the Eq. (3.59) tower. -/
noncomputable def CMP99SourceActiveRegionChain.retainedFineComplexOneCochain
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (A : PhysicalGaugeOneCochain d N Nc) :
    CMP99Eq337PhysicalComplexOneCochain d N Nc :=
  cmp99Eq337PhysicalComplexifyOneCochain
    (regions.retainedFineOneCochainExtension A)

@[simp] theorem CMP99SourceActiveRegionChain.retainedFineComplexOneCochain_apply_of_mem
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d N)
    (hb : b ∈ regions.retainedFineReadBonds (Nc := Nc)) :
    regions.retainedFineComplexOneCochain A b =
      cmp99SUNLieCoordComplexificationLM Nc (A b) := by
  simp [CMP99SourceActiveRegionChain.retainedFineComplexOneCochain, hb]

@[simp] theorem CMP99SourceActiveRegionChain.retainedFineComplexOneCochain_apply_of_not_mem
    (regions : CMP99SourceActiveRegionChain d M N Omega depth)
    (A : PhysicalGaugeOneCochain d N Nc) (b : PhysicalBond d N)
    (hb : b ∉ regions.retainedFineReadBonds (Nc := Nc)) :
    regions.retainedFineComplexOneCochain A b = 0 := by
  simp [CMP99SourceActiveRegionChain.retainedFineComplexOneCochain, hb]

end

end YangMills.RG
