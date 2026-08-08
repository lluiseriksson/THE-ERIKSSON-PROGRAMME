/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80SourcePi4SecondFieldDerivativeBound
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Source-faithful decomposition of the equation-(80) outer jet

The quantitative source-domain estimate previously retained the norm of the
full joint iterated derivative of the literal equation-(80) potential.  This
file decomposes that derivative into the four terms printed in CMP102:

* the `D₃` source pairing;
* the `D` transport pairing;
* the quadratic `D` pairing;
* the composed `V₀` remainder.

The terminal bound is an application of the triangle inequality to an exact
identity of iterated Fréchet derivatives.  It introduces no domain-Hessian
hypothesis, no numerical majorant for the complete joint jet, and no
factorial or ambient-dimension loss.

Honest scope: the four component jets remain literal derivatives.  Bounding
them quantitatively from source estimates on `D`, `D₃`, and `V₀` is the next
analytic layer toward equation (1.43).
-/

open scoped RealInnerProductSpace

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev JointSpace := (F →L[ℝ] E) × E

/-- The first literal term of equation (80), containing `D₃` and the source
`J`. -/
noncomputable def cmp102Eq80JointSourceTerm
    (D₃ : E → F) (J : E) (p : JointSpace (E := E) (F := F)) : ℝ :=
  - inner ℝ (p.1 (D₃ p.2)) J

/-- The second literal term of equation (80), containing the transport
pairing with `Δπ`. -/
noncomputable def cmp102Eq80JointTransportTerm
    (D : E → F) (Δπ : E →L[ℝ] E)
    (p : JointSpace (E := E) (F := F)) : ℝ :=
  - inner ℝ p.2 (Δπ (p.1 (D p.2)))

/-- The third literal term of equation (80), the quadratic pairing in
`H (D A)`. -/
noncomputable def cmp102Eq80JointQuadraticTerm
    (D : E → F) (Δπ : E →L[ℝ] E)
    (p : JointSpace (E := E) (F := F)) : ℝ :=
  (1 / 2 : ℝ) * inner ℝ (p.1 (D p.2)) (Δπ (p.1 (D p.2)))

/-- The fourth literal term of equation (80), the composed `V₀` remainder. -/
noncomputable def cmp102Eq80JointRemainderTerm
    (D : E → F) (V₀ : E → ℝ)
    (p : JointSpace (E := E) (F := F)) : ℝ :=
  V₀ (p.2 - p.1 (D p.2))

/-- The literal equation-(80) potential is pointwise the sum of its four
source components. -/
theorem cmp102Eq80GlobalPotential_eq_jointTermSum
    (D D₃ : E → F) (V₀ : E → ℝ)
    (H : F →L[ℝ] E) (Δπ : E →L[ℝ] E) (J A : E) :
    cmp102Eq80GlobalPotential D D₃ V₀ H Δπ J A =
      cmp102Eq80JointSourceTerm D₃ J (H, A) +
      cmp102Eq80JointTransportTerm D Δπ (H, A) +
      cmp102Eq80JointQuadraticTerm D Δπ (H, A) +
      cmp102Eq80JointRemainderTerm D V₀ (H, A) := by
  simp only [cmp102Eq80GlobalPotential, cmp102Eq80JointSourceTerm,
    cmp102Eq80JointTransportTerm, cmp102Eq80JointQuadraticTerm,
    cmp102Eq80JointRemainderTerm, sub_eq_add_neg]

/-- The source term is smooth when `D₃` is smooth. -/
theorem contDiff_top_cmp102Eq80JointSourceTerm
    (D₃ : E → F) (J : E) (hD₃ : ContDiff ℝ ⊤ D₃) :
    ContDiff ℝ ⊤ (cmp102Eq80JointSourceTerm D₃ J) := by
  unfold cmp102Eq80JointSourceTerm
  exact (contDiff_fst.clm_apply (hD₃.comp contDiff_snd)).inner ℝ contDiff_const |>.neg

/-- The transport term is smooth when `D` is smooth. -/
theorem contDiff_top_cmp102Eq80JointTransportTerm
    (D : E → F) (Δπ : E →L[ℝ] E) (hD : ContDiff ℝ ⊤ D) :
    ContDiff ℝ ⊤ (cmp102Eq80JointTransportTerm D Δπ) := by
  unfold cmp102Eq80JointTransportTerm
  have hHD : ContDiff ℝ ⊤
      (fun p : JointSpace (E := E) (F := F) => p.1 (D p.2)) :=
    contDiff_fst.clm_apply (hD.comp contDiff_snd)
  exact (contDiff_snd.inner ℝ (Δπ.contDiff.comp hHD)).neg

/-- The quadratic term is smooth when `D` is smooth. -/
theorem contDiff_top_cmp102Eq80JointQuadraticTerm
    (D : E → F) (Δπ : E →L[ℝ] E) (hD : ContDiff ℝ ⊤ D) :
    ContDiff ℝ ⊤ (cmp102Eq80JointQuadraticTerm D Δπ) := by
  unfold cmp102Eq80JointQuadraticTerm
  have hHD : ContDiff ℝ ⊤
      (fun p : JointSpace (E := E) (F := F) => p.1 (D p.2)) :=
    contDiff_fst.clm_apply (hD.comp contDiff_snd)
  exact contDiff_const.mul (hHD.inner ℝ (Δπ.contDiff.comp hHD))

/-- The remainder term is smooth when both `D` and `V₀` are smooth. -/
theorem contDiff_top_cmp102Eq80JointRemainderTerm
    (D : E → F) (V₀ : E → ℝ)
    (hD : ContDiff ℝ ⊤ D) (hV₀ : ContDiff ℝ ⊤ V₀) :
    ContDiff ℝ ⊤ (cmp102Eq80JointRemainderTerm D V₀) := by
  unfold cmp102Eq80JointRemainderTerm
  have hHD : ContDiff ℝ ⊤
      (fun p : JointSpace (E := E) (F := F) => p.1 (D p.2)) :=
    contDiff_fst.clm_apply (hD.comp contDiff_snd)
  exact hV₀.comp (contDiff_snd.sub hHD)

/-- The explicit componentwise outer-jet majorant for equation (80). -/
noncomputable def cmp102Eq80JointComponentJetMajorant
    (D D₃ : E → F) (V₀ : E → ℝ)
    (Δπ : E →L[ℝ] E) (J : E) (n : ℕ)
    (p : JointSpace (E := E) (F := F)) : ℝ :=
  ‖iteratedFDeriv ℝ n (cmp102Eq80JointSourceTerm D₃ J) p‖ +
  ‖iteratedFDeriv ℝ n (cmp102Eq80JointTransportTerm D Δπ) p‖ +
  ‖iteratedFDeriv ℝ n (cmp102Eq80JointQuadraticTerm D Δπ) p‖ +
  ‖iteratedFDeriv ℝ n (cmp102Eq80JointRemainderTerm D V₀) p‖

/-- The full outer joint jet is bounded by the sum of the four literal
component jets.  This is the source-faithful replacement for treating the
complete equation-(80) derivative as one opaque analytic input. -/
theorem norm_iteratedFDeriv_cmp102Eq80JointPotential_le_componentJetMajorant
    (D D₃ : E → F) (V₀ : E → ℝ)
    (Δπ : E →L[ℝ] E) (J : E)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (n : ℕ) (p : JointSpace (E := E) (F := F)) :
    ‖iteratedFDeriv ℝ n
        (fun q : JointSpace (E := E) (F := F) =>
          cmp102Eq80GlobalPotential D D₃ V₀ q.1 Δπ J q.2) p‖ ≤
      cmp102Eq80JointComponentJetMajorant D D₃ V₀ Δπ J n p := by
  have h₁ : ContDiff ℝ ⊤ (cmp102Eq80JointSourceTerm D₃ J) :=
    contDiff_top_cmp102Eq80JointSourceTerm D₃ J hD₃
  have h₂ : ContDiff ℝ ⊤ (cmp102Eq80JointTransportTerm D Δπ) :=
    contDiff_top_cmp102Eq80JointTransportTerm D Δπ hD
  have h₃ : ContDiff ℝ ⊤ (cmp102Eq80JointQuadraticTerm D Δπ) :=
    contDiff_top_cmp102Eq80JointQuadraticTerm D Δπ hD
  have h₄ : ContDiff ℝ ⊤ (cmp102Eq80JointRemainderTerm D V₀) :=
    contDiff_top_cmp102Eq80JointRemainderTerm D V₀ hD hV₀
  have h₁n : ContDiffAt ℝ n
      (cmp102Eq80JointSourceTerm D₃ J) p :=
    h₁.contDiffAt.of_le le_top
  have h₂n : ContDiffAt ℝ n
      (cmp102Eq80JointTransportTerm D Δπ) p :=
    h₂.contDiffAt.of_le le_top
  have h₃n : ContDiffAt ℝ n
      (cmp102Eq80JointQuadraticTerm D Δπ) p :=
    h₃.contDiffAt.of_le le_top
  have h₄n : ContDiffAt ℝ n
      (cmp102Eq80JointRemainderTerm D V₀) p :=
    h₄.contDiffAt.of_le le_top
  have hfun :
      (fun q : JointSpace (E := E) (F := F) =>
        cmp102Eq80GlobalPotential D D₃ V₀ q.1 Δπ J q.2) =
        (((cmp102Eq80JointSourceTerm D₃ J +
            cmp102Eq80JointTransportTerm D Δπ) +
          cmp102Eq80JointQuadraticTerm D Δπ) +
          cmp102Eq80JointRemainderTerm D V₀) := by
    funext q
    exact cmp102Eq80GlobalPotential_eq_jointTermSum
      D D₃ V₀ q.1 Δπ J q.2
  rw [hfun]
  change
    ‖iteratedFDeriv ℝ n
        (fun q =>
          ((cmp102Eq80JointSourceTerm D₃ J q +
              cmp102Eq80JointTransportTerm D Δπ q) +
            cmp102Eq80JointQuadraticTerm D Δπ q) +
            cmp102Eq80JointRemainderTerm D V₀ q) p‖ ≤
      cmp102Eq80JointComponentJetMajorant D D₃ V₀ Δπ J n p
  have houter :
      iteratedFDeriv ℝ n
          (fun q =>
            ((cmp102Eq80JointSourceTerm D₃ J q +
                cmp102Eq80JointTransportTerm D Δπ q) +
              cmp102Eq80JointQuadraticTerm D Δπ q) +
              cmp102Eq80JointRemainderTerm D V₀ q) p =
        iteratedFDeriv ℝ n
            (fun q =>
              (cmp102Eq80JointSourceTerm D₃ J q +
                cmp102Eq80JointTransportTerm D Δπ q) +
                cmp102Eq80JointQuadraticTerm D Δπ q) p +
          iteratedFDeriv ℝ n
            (cmp102Eq80JointRemainderTerm D V₀) p := by
    simpa only [Pi.add_apply] using
      iteratedFDeriv_add_apply ((h₁n.add h₂n).add h₃n) h₄n
  rw [houter]
  have hmiddle :
      iteratedFDeriv ℝ n
          (fun q =>
            (cmp102Eq80JointSourceTerm D₃ J q +
              cmp102Eq80JointTransportTerm D Δπ q) +
              cmp102Eq80JointQuadraticTerm D Δπ q) p =
        iteratedFDeriv ℝ n
            (fun q =>
              cmp102Eq80JointSourceTerm D₃ J q +
                cmp102Eq80JointTransportTerm D Δπ q) p +
          iteratedFDeriv ℝ n
            (cmp102Eq80JointQuadraticTerm D Δπ) p := by
    simpa only [Pi.add_apply] using
      iteratedFDeriv_add_apply (h₁n.add h₂n) h₃n
  rw [hmiddle]
  have hinner :
      iteratedFDeriv ℝ n
          (fun q =>
            cmp102Eq80JointSourceTerm D₃ J q +
              cmp102Eq80JointTransportTerm D Δπ q) p =
        iteratedFDeriv ℝ n (cmp102Eq80JointSourceTerm D₃ J) p +
          iteratedFDeriv ℝ n
            (cmp102Eq80JointTransportTerm D Δπ) p := by
    simpa only [Pi.add_apply] using
      iteratedFDeriv_add_apply h₁n h₂n
  rw [hinner]
  have four_norm_le
      (a b c d :
        ContinuousMultilinearMap ℝ
          (fun _ : Fin n => JointSpace (E := E) (F := F)) ℝ) :
      ‖((a + b) + c) + d‖ ≤ ((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖ := by
    calc
      ‖((a + b) + c) + d‖ ≤ ‖(a + b) + c‖ + ‖d‖ :=
        norm_add_le ((a + b) + c) d
      _ ≤ (‖a + b‖ + ‖c‖) + ‖d‖ :=
        by linarith [norm_add_le (a + b) c]
      _ ≤ ((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖ :=
        by linarith [norm_add_le a b]
  unfold cmp102Eq80JointComponentJetMajorant
  exact four_norm_le
    (iteratedFDeriv ℝ n (cmp102Eq80JointSourceTerm D₃ J) p)
    (iteratedFDeriv ℝ n (cmp102Eq80JointTransportTerm D Δπ) p)
    (iteratedFDeriv ℝ n (cmp102Eq80JointQuadraticTerm D Δπ) p)
    (iteratedFDeriv ℝ n (cmp102Eq80JointRemainderTerm D V₀) p)

end

end YangMills.RG
