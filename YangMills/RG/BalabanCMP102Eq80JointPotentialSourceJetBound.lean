/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP102Eq80JointRemainderTermJetBound

/-!
# Source-generated quantitative jet bound for equation (80)

This module composes the four quantitative producers for the literal terms
of CMP102 equation (80).  The terminal majorant is generated from:

* derivatives of `D₃` for the source pairing;
* derivatives of `D` and `‖Δπ‖` for the transport and quadratic pairings;
* derivatives of `V₀` and the explicit inner-map budget for the remainder.

The result replaces the earlier sum of four unevaluated component norms by a
single source-level bound.  It does not assume a bound for the complete
equation-(80) jet or for a domain Hessian.
-/

namespace YangMills.RG

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private abbrev JointSpace := (F →L[ℝ] E) × E

/-- Explicit majorant for the literal `D₃` source term. -/
noncomputable def cmp102Eq80JointSourceTermJetMajorant
    (D₃ : E → F) (J : E) (n : ℕ)
    (p : JointSpace (E := E) (F := F)) : ℝ :=
  ‖J‖ *
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i
          (fun q : JointSpace (E := E) (F := F) => q.1) p‖ *
        ‖iteratedFDeriv ℝ (n - i)
          (fun q : JointSpace (E := E) (F := F) => D₃ q.2) p‖

/-- Explicit majorant for the literal transport term. -/
noncomputable def cmp102Eq80JointTransportTermJetMajorant
    (D : E → F) (Δπ : E →L[ℝ] E) (n : ℕ)
    (p : JointSpace (E := E) (F := F)) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i
        (fun q : JointSpace (E := E) (F := F) => q.2) p‖ *
      (‖Δπ‖ *
        cmp102Eq80JointEvaluationJetMajorant D (n - i) p)

/-- Explicit majorant for the literal quadratic term. -/
noncomputable def cmp102Eq80JointQuadraticTermJetMajorant
    (D : E → F) (Δπ : E →L[ℝ] E) (n : ℕ)
    (p : JointSpace (E := E) (F := F)) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) *
        cmp102Eq80JointEvaluationJetMajorant D i p *
        (‖Δπ‖ *
          cmp102Eq80JointEvaluationJetMajorant D (n - i) p)

/-- Complete source-generated majorant for the joint jet of equation (80). -/
noncomputable def cmp102Eq80JointPotentialSourceJetMajorant
    (D D₃ : E → F) (Δπ : E →L[ℝ] E) (J : E)
    (n : ℕ) (p : JointSpace (E := E) (F := F))
    (C R : ℝ) : ℝ :=
  cmp102Eq80JointSourceTermJetMajorant D₃ J n p +
  cmp102Eq80JointTransportTermJetMajorant D Δπ n p +
  cmp102Eq80JointQuadraticTermJetMajorant D Δπ n p +
  (n.factorial : ℝ) * C * R ^ n

/-- The complete literal equation-(80) jet is bounded by the sum of the
four source-generated majorants. -/
theorem norm_iteratedFDeriv_cmp102Eq80JointPotential_le_sourceJetMajorant
    (D D₃ : E → F) (V₀ : E → ℝ)
    (Δπ : E →L[ℝ] E) (J : E)
    (hD : ContDiff ℝ ⊤ D) (hD₃ : ContDiff ℝ ⊤ D₃)
    (hV₀ : ContDiff ℝ ⊤ V₀)
    (n : ℕ) (p : JointSpace (E := E) (F := F))
    (C R : ℝ)
    (hC : ∀ i, i ≤ n →
      ‖iteratedFDeriv ℝ i V₀
        (cmp102Eq80JointRemainderInner D p)‖ ≤ C)
    (hR : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDeriv ℝ i
        (fun q : JointSpace (E := E) (F := F) => q.2) p‖ +
        cmp102Eq80JointEvaluationJetMajorant D i p ≤ R ^ i) :
    ‖iteratedFDeriv ℝ n
        (fun q : JointSpace (E := E) (F := F) =>
          cmp102Eq80GlobalPotential D D₃ V₀ q.1 Δπ J q.2) p‖ ≤
      cmp102Eq80JointPotentialSourceJetMajorant
        D D₃ Δπ J n p C R := by
  have hsource :
      ‖iteratedFDeriv ℝ n
        (cmp102Eq80JointSourceTerm D₃ J) p‖ ≤
        cmp102Eq80JointSourceTermJetMajorant D₃ J n p := by
    unfold cmp102Eq80JointSourceTermJetMajorant
    exact norm_iteratedFDeriv_cmp102Eq80JointSourceTerm_le
      D₃ J hD₃ n p
  have htransport :
      ‖iteratedFDeriv ℝ n
        (cmp102Eq80JointTransportTerm D Δπ) p‖ ≤
        cmp102Eq80JointTransportTermJetMajorant D Δπ n p := by
    unfold cmp102Eq80JointTransportTermJetMajorant
    simpa [cmp102Eq80JointEvaluationJetMajorant] using
      norm_iteratedFDeriv_cmp102Eq80JointTransportTerm_le
        D Δπ hD n p
  have hquadratic :
      ‖iteratedFDeriv ℝ n
        (cmp102Eq80JointQuadraticTerm D Δπ) p‖ ≤
        cmp102Eq80JointQuadraticTermJetMajorant D Δπ n p := by
    exact norm_iteratedFDeriv_cmp102Eq80JointQuadraticTerm_le
      D Δπ hD n p
  have hremainder :
      ‖iteratedFDeriv ℝ n
        (cmp102Eq80JointRemainderTerm D V₀) p‖ ≤
        (n.factorial : ℝ) * C * R ^ n :=
    norm_iteratedFDeriv_cmp102Eq80JointRemainderTerm_le
      D V₀ hD hV₀ n p C R hC hR
  calc
    ‖iteratedFDeriv ℝ n
        (fun q : JointSpace (E := E) (F := F) =>
          cmp102Eq80GlobalPotential D D₃ V₀ q.1 Δπ J q.2) p‖ ≤
        cmp102Eq80JointComponentJetMajorant
          D D₃ V₀ Δπ J n p :=
      norm_iteratedFDeriv_cmp102Eq80JointPotential_le_componentJetMajorant
        D D₃ V₀ Δπ J hD hD₃ hV₀ n p
    _ ≤
        cmp102Eq80JointPotentialSourceJetMajorant
          D D₃ Δπ J n p C R := by
      unfold cmp102Eq80JointComponentJetMajorant
      unfold cmp102Eq80JointPotentialSourceJetMajorant
      exact add_le_add
        (add_le_add (add_le_add hsource htransport) hquadratic)
        hremainder

end

end YangMills.RG
