/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq249FinePhaseScaleNoGo
import YangMills.RG.BalabanCMP99SourceFlatQprimeCoarseAlias

/-!
# Fine-to-coarse endpoint phase below the generated flat Green synthesis

PRE-VALIDATION: this source is present, its `.olean` has not yet been
materialized, and its declarations have not yet been compiler verified.

The positive fine Fourier character at `x`, divided by its value at the
canonical block basepoint of `y`, is identified with the literal CMP89 entire
phase.  The endpoint displacement is the integer vector `M*y-x`, while the
fine-to-block conversion remains visible as the factor `M⁻¹` in
`cmp89Eq249PhysicalFineLatticeDisplacement`.

This is only the endpoint unit/phase dictionary.  It does not reindex a
signed-alias fibre, identify the finite synthesis with a Brillouin integral,
produce regional `B0`, attain window 15, discharge a terminal field, or
inhabit `TermSource`.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N' : ℕ}

/-- Integer displacement from a fine endpoint to the canonical basepoint of
one coarse endpoint.  Its sign is chosen so that multiplication by the
source amplitude momentum `-M*p` gives the positive Fourier phase
`p*(x-M*y)` after the explicit `M⁻¹` conversion. -/
def cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
    (M : ℕ) (x : FinBox d (M * N')) (y : FinBox d N') : Fin d → ℤ :=
  fun mu ↦ ((M * (y mu).val : ℕ) : ℤ) - ((x mu).val : ℤ)

/-- One coordinate of the positive flat Fourier character is the literal
complex exponential at the discrete momentum and the canonical natural site
representative. -/
theorem cmp99Flat_stdAddChar_mul_eq_exp_discreteMomentum
    {N : ℕ} [NeZero N] (k x : FinBox d N) (mu : Fin d) :
    ZMod.stdAddChar
        (((k mu).val : ZMod N) * ((x mu).val : ZMod N)) =
      Complex.exp
        (Complex.I * (cmp99FlatDiscreteMomentum k mu : ℂ) * (x mu).val) := by
  have h := ZMod.stdAddChar_coe (N := N)
    ((((k mu).val * (x mu).val : ℕ) : ℤ))
  convert h using 1
  · push_cast
    ring
  · unfold cmp99FlatDiscreteMomentum
    push_cast
    have hN : (N : ℂ) ≠ 0 := by
      exact_mod_cast (NeZero.ne N)
    field_simp [hN]

/-- The positive flat Fourier mode is the exact entire phase at the canonical
integer lift of its periodic site. -/
theorem cmp99FlatFourierMode_eq_exp_entirePhase_canonicalLift
    {N : ℕ} [NeZero N] (k x : FinBox d N) :
    cmp99FlatFourierMode k x =
      Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (fun mu ↦ (cmp99FlatDiscreteMomentum k mu : ℂ))
          (cmp89Eq251LatticeDisplacement
            (fun mu ↦ ((x mu).val : ℤ)))) := by
  rw [cmp99FlatFourierMode_eq_coordinateProduct]
  simp_rw [cmp99Flat_stdAddChar_mul_eq_exp_discreteMomentum]
  rw [← Complex.exp_sum]
  congr 2
  simp only [cmp89Eq251EntirePhase, cmp89Eq251LatticeDisplacement]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  ring

/-- Exact fine-to-coarse endpoint phase.  The scale conversion is a theorem,
not a convention: the amplitude momentum is `-M` times the fine momentum and
the endpoint displacement carries the compensating factor `M⁻¹`. -/
theorem cmp99FlatFourierMode_div_coarseMode_eq_exp_amplitudeMomentum_endpoint
    [NeZero M] [NeZero N']
    (k : FinBox d (M * N')) (x : FinBox d (M * N')) (y : FinBox d N') :
    cmp99FlatFourierMode k x *
        (cmp99FlatFourierMode
          (cmp99SourceFlatQprimeCoarseAlias k) y)⁻¹ =
      Complex.exp
        (Complex.I * cmp89Eq251EntirePhase
          (cmp99SourceFlatQprimeAmplitudeMomentum k)
          (cmp89Eq249PhysicalFineLatticeDisplacement
            ((M : ℝ)⁻¹)
            (cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement M x y))) := by
  rw [← cmp99FlatFourierMode_blockBasepoint_eq_coarseAlias k y,
    cmp99FlatFourierMode_eq_exp_entirePhase_canonicalLift,
    cmp99FlatFourierMode_eq_exp_entirePhase_canonicalLift,
    ← Complex.exp_neg, ← Complex.exp_add]
  congr 2
  simp only [cmp89Eq251EntirePhase, cmp89Eq251LatticeDisplacement,
    cmp89Eq249PhysicalFineLatticeDisplacement,
    cmp99SourceFlatQprimeAmplitudeMomentum,
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement,
    cmp99FlatDiscreteMomentum, blockBasepoint]
  have hM : (M : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  rw [← sub_eq_add_neg, ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mu _
  push_cast
  field_simp [hM]
  ring

end

end YangMills.RG
