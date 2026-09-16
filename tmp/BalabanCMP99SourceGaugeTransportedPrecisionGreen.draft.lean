import YangMills.RG.BalabanCMP99SourceGaugeTransportedRetainedPair
import YangMills.RG.BalabanCMP99SourcePhysicalGaugePrecision

/-!
PRE-VALIDATION: source is present only in scratch; no `.olean` has been
materialized and none of the declarations below is compiler-verified.

# Gauge transport of the literal CMP99 precision and Green

This is C6c.8d.  The precision on the regular background is built from the
regular member of the private retained pair.  Its transformed counterpart is
built from the small member.  Precision covariance follows from the already
derived D0 and multiscale-Qprime intertwiners; Green covariance then follows
from exact inverse uniqueness.  No Green or precision equality is an input.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N Nc depth : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]
variable {Omega : ActiveGaugeRegion d N}
variable {regions : CMP99SourceActiveRegionChain d M N Omega depth}
variable {hd : 2 ≤ d} {hM : 2 ≤ M} {rho : SUNAdjointModel Nc}
variable {spacing epsilon : ℝ}
variable {background : GaugeConfig d N (SUN Nc)}
variable {u : GaugeTransform d N (SUN Nc)}
variable {chain : CMP99SourceUbarRadiusChain d M Nc depth epsilon}
variable {transformedSmall : ∀ e : ConcreteEdge d N,
  ‖(gaugeAct u background e : Matrix (Fin Nc) (Fin Nc) ℂ) - 1‖ ≤ epsilon}

namespace CMP99SourceGaugeTransportedRetainedPair

/-- Literal regular-background precision using the internally generated
terminal retained `Qprime`. -/
noncomputable def originalPrecision
    (T : CMP99SourceGaugeTransportedRetainedPair regions hd hM rho spacing
      epsilon background u chain transformedSmall)
    (a : ℝ) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  cmp99SourceGaugePrecision
    (cmp99ActiveRegionSourceCovariantLaplacian Omega rho background spacing)
    (T.originalTowerAt (Fin.last depth)).Qprime a

/-- Literal precision on the small gauge representative. -/
noncomputable def transformedPrecision
    (T : CMP99SourceGaugeTransportedRetainedPair regions hd hM rho spacing
      epsilon background u chain transformedSmall)
    (a : ℝ) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  cmp99SourceGaugePrecision
    (cmp99ActiveRegionSourceCovariantLaplacian Omega rho
      (gaugeAct u background) spacing)
    (T.transformedTowerAt (Fin.last depth)).Qprime a

/-- The two literal precisions intertwine through the fine regional gauge
isometry.  Both the Laplacian and `Qprime†Qprime` contributions are derived
separately before their sum is formed. -/
theorem transformedPrecision_comp_gaugeIsometry
    (T : CMP99SourceGaugeTransportedRetainedPair regions hd hM rho spacing
      epsilon background u chain transformedSmall)
    (a : ℝ) :
    (T.transformedPrecision a).comp
        (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u :
          ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
            ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) =
      (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u :
        ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
          ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)).comp
        (T.originalPrecision a) := by
  let E := cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u
  let F := T.prefixGauge (Fin.last depth)
  let Q := (T.originalTowerAt (Fin.last depth)).Qprime
  let Q' := (T.transformedTowerAt (Fin.last depth)).Qprime
  have hQ : Q'.comp (E : _ →L[ℝ] _) = (F : _ →L[ℝ] _).comp Q :=
    T.terminalQprime_intertwines
  have hmass :=
    continuousLinearMap_adjoint_comp_self_intertwines_of_isometries
      Q Q' E F hQ
  apply ContinuousLinearMap.ext
  intro phi
  have hDelta := cmp99ActiveRegionSourceCovariantLaplacian_gaugeAct
    Omega rho u background spacing phi
  have hmassPhi := congrArg
    (fun A : ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
        ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) => A phi) hmass
  change Q'.adjoint (Q' (E phi)) = E (Q.adjoint (Q phi)) at hmassPhi
  change
    cmp99ActiveRegionSourceCovariantLaplacian Omega rho
          (gaugeAct u background) spacing (E phi) +
        a • Q'.adjoint (Q' (E phi)) =
      E (cmp99ActiveRegionSourceCovariantLaplacian Omega rho background
          spacing phi + a • Q.adjoint (Q phi))
  rw [hDelta, hmassPhi, map_add, map_smul]

/-- Coercivity of the canonical small representative produces coercivity of
the regular-background precision with exactly the same constant. -/
theorem isCoerciveCLM_originalPrecision
    (T : CMP99SourceGaugeTransportedRetainedPair regions hd hM rho spacing
      epsilon background u chain transformedSmall)
    (a c : ℝ) (htransformed : IsCoerciveCLM (T.transformedPrecision a) c) :
    IsCoerciveCLM (T.originalPrecision a) c :=
  isCoerciveCLM_of_intertwines_linearIsometryEquiv
    (T.originalPrecision a) (T.transformedPrecision a)
    (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u)
    (T.transformedPrecision_comp_gaugeIsometry a) htransformed

/-- The regular Green is constructed as the inverse of the internally
generated regular precision. -/
noncomputable def originalGreen
    (T : CMP99SourceGaugeTransportedRetainedPair regions hd hM rho spacing
      epsilon background u chain transformedSmall)
    (a : ℝ) {c : ℝ} (hc : 0 < c)
    (htransformed : IsCoerciveCLM (T.transformedPrecision a) c) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  covarianceOfIsCoerciveCLM (T.originalPrecision a) hc
    (T.isCoerciveCLM_originalPrecision a c htransformed)

/-- The small-side Green is the inverse of the literal transformed
precision. -/
noncomputable def transformedGreen
    (T : CMP99SourceGaugeTransportedRetainedPair regions hd hM rho spacing
      epsilon background u chain transformedSmall)
    (a : ℝ) {c : ℝ} (hc : 0 < c)
    (htransformed : IsCoerciveCLM (T.transformedPrecision a) c) :
    ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
      ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) :=
  covarianceOfIsCoerciveCLM (T.transformedPrecision a) hc htransformed

end CMP99SourceGaugeTransportedRetainedPair

/-- Exact inverses inherit an isometric intertwiner from their precisions.
The conclusion is proved by injectivity of the transformed precision, not by
accepting an equality between inverse operators. -/
theorem covarianceOfIsCoerciveCLM_intertwines_of_precision_intertwines
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (A A' : E →L[ℝ] E) (e : E ≃ₗᵢ[ℝ] E) {c : ℝ} (hc : 0 < c)
    (hA : IsCoerciveCLM A c) (hA' : IsCoerciveCLM A' c)
    (hintertwines : A'.comp (e : E →L[ℝ] E) =
      (e : E →L[ℝ] E).comp A) :
    (covarianceOfIsCoerciveCLM A' hc hA').comp (e : E →L[ℝ] E) =
      (e : E →L[ℝ] E).comp (covarianceOfIsCoerciveCLM A hc hA) := by
  apply ContinuousLinearMap.ext
  intro x
  apply isCoerciveCLM_injective A' hc hA'
  have hintertwinesX := congrArg (fun T : E →L[ℝ] E =>
    T (covarianceOfIsCoerciveCLM A hc hA x)) hintertwines
  change A' (e (covarianceOfIsCoerciveCLM A hc hA x)) =
    e (A (covarianceOfIsCoerciveCLM A hc hA x)) at hintertwinesX
  change
    A' (covarianceOfIsCoerciveCLM A' hc hA' (e x)) =
      A' (e (covarianceOfIsCoerciveCLM A hc hA x))
  calc
    A' (covarianceOfIsCoerciveCLM A' hc hA' (e x)) = e x :=
      precision_apply_covarianceOfIsCoerciveCLM A' hc hA' (e x)
    _ = e (A (covarianceOfIsCoerciveCLM A hc hA x)) := by
      rw [precision_apply_covarianceOfIsCoerciveCLM A hc hA x]
    _ = A' (e (covarianceOfIsCoerciveCLM A hc hA x)) :=
      hintertwinesX.symm

namespace CMP99SourceGaugeTransportedRetainedPair

/-- The two internally constructed Green operators satisfy CMP99 (3.31) by
inverse uniqueness. -/
theorem transformedGreen_comp_gaugeIsometry
    (T : CMP99SourceGaugeTransportedRetainedPair regions hd hM rho spacing
      epsilon background u chain transformedSmall)
    (a : ℝ) {c : ℝ} (hc : 0 < c)
    (htransformed : IsCoerciveCLM (T.transformedPrecision a) c) :
    (T.transformedGreen a hc htransformed).comp
        (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u :
          ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
            ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)) =
      (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u :
        ActiveGaugeZeroCochain Omega (SUNLieCoord Nc) →L[ℝ]
          ActiveGaugeZeroCochain Omega (SUNLieCoord Nc)).comp
        (T.originalGreen a hc htransformed) := by
  exact covarianceOfIsCoerciveCLM_intertwines_of_precision_intertwines
    (T.originalPrecision a) (T.transformedPrecision a)
    (cmp99RegionalFineGaugeLinearIsometryEquiv Omega rho u) hc
    (T.isCoerciveCLM_originalPrecision a c htransformed) htransformed
    (T.transformedPrecision_comp_gaugeIsometry a)

end CMP99SourceGaugeTransportedRetainedPair

end

end YangMills.RG
