import YangMills.RG.BalabanCMP99PhysicalUbarGaugeCovariance
import YangMills.RG.BalabanCMP99SourceRegionalScale
import YangMills.RG.BalabanCMP98ContourExponentialTransport
import YangMills.RG.BalabanCMP98PhysicalSpecialUnitaryChart

/-!
PRE-VALIDATION: source is present only in scratch; no `.olean` has been
materialized and none of the declarations below is compiler-verified.

# Gauge transport of the literal CMP99 source deviation

This is the C6c.8c1--c2 prefix.  It derives the two facts needed to construct
the source-normalized scale on a regular background from the canonical small
representative.  No original-side smallness or deviation bound is accepted.
-/

namespace YangMills.RG

open YangMills YangMills.GaugeConfig Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d M N' Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N'] [NeZero Nc]

/-- Conjugation by a special-unitary matrix preserves the concrete L2 matrix
operator norm.  The reverse inequality is the already sealed contractive
bound applied to the inverse element. -/
theorem norm_sun_conj_matrix_eq
    (p : SUN Nc) (X : Matrix (Fin Nc) (Fin Nc) ℂ) :
    ‖(p : Matrix (Fin Nc) (Fin Nc) ℂ) * X *
        Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ)‖ = ‖X‖ := by
  apply le_antisymm
  · exact norm_sun_conj_matrix_le p X
  · let Y := (p : Matrix (Fin Nc) (Fin Nc) ℂ) * X *
      Matrix.conjTranspose (p : Matrix (Fin Nc) (Fin Nc) ℂ)
    have hreverse := norm_sun_conj_matrix_le p⁻¹ Y
    have hcollapse :
        ((p⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) * Y *
            Matrix.conjTranspose
              ((p⁻¹ : SUN Nc) : Matrix (Fin Nc) (Fin Nc) ℂ) = X := by
      dsimp [Y]
      rw [coe_sun_inv_eq_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc, su_conjTranspose_mul_self,
        Matrix.mul_one]
    rw [hcollapse] at hreverse
    exact hreverse

/-- The literal no-winding argument has exactly the same norm before and
after gauge transformation.  All path endpoint hypotheses are the printed
source hypotheses consumed by `UbarDeviationLogArg_gaugeAct`. -/
theorem norm_UbarDeviationLogArg_gaugeAct_eq
    (u : GaugeTransform d (M * N') (SUN Nc))
    (A_fine : GaugeConfig d (M * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (C : ConcreteEdge d N') (x : FinBox d (M * N'))
    (Gamma1 Gamma2 Gamma3 :
      FinBox d (M * N') → List (ConcreteEdge d (M * N')))
    (hpath1 : IsPathFrom
      (blockBasepoint M N' (FiniteLatticeGeometry.src C)) (Gamma1 x))
    (hend1 : pathEnd
      (blockBasepoint M N' (FiniteLatticeGeometry.src C)) (Gamma1 x) = x)
    (hpath2 : IsPathFrom x (Gamma2 x))
    (hpath3 : IsPathFrom (pathEnd x (Gamma2 x)) (Gamma3 x))
    (hend3 : pathEnd (pathEnd x (Gamma2 x)) (Gamma3 x) =
      blockBasepoint M N' (FiniteLatticeGeometry.dst C)) :
    ‖UbarDeviationLogArg
        (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
        C x Gamma1 Gamma2 Gamma3‖ =
      ‖UbarDeviationLogArg
        (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        A_fine A_coarse C x Gamma1 Gamma2 Gamma3‖ := by
  rw [UbarDeviationLogArg_gaugeAct
    (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
    u A_fine A_coarse C x Gamma1 Gamma2 Gamma3
    hpath1 hend1 hpath2 hpath3 hend3]
  let p : SUN Nc := u (blockBasepoint M N' (FiniteLatticeGeometry.src C))
  let X := UbarDeviationLogArg
    (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
    A_fine A_coarse C x Gamma1 Gamma2 Gamma3
  change ‖(MatrixRealization.rep p).val * X *
      ((MatrixRealization.rep p)⁻¹).val‖ = ‖X‖
  rw [← map_inv]
  simp only [matrixRealizationSUN_val, coe_sun_inv_eq_conjTranspose]
  exact norm_sun_conj_matrix_eq p X

/-- Forgetting the direct-budget determinant certificate recovers the same
literal matrix `Ubar` as the older common-radius constructor. -/
theorem cmp99PhysicalUbarBlockOfDeviationBudget_coe_eq_Ubar
    (A_fine : GaugeConfig d (M * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Gamma1 Gamma2 Gamma3 : PhysicalBond d N' →
      FinBox d (M * N') → List (ConcreteEdge d (M * N')))
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
          (Gamma1 b) (Gamma2 b) (Gamma3 b)‖ ≤ B.δ)
    (b : PhysicalBond d N') :
    (cmp99PhysicalUbarBlockOfDeviationBudget
        A_fine A_coarse Gamma1 Gamma2 Gamma3 B hdev b :
          Matrix (Fin Nc) (Fin Nc) ℂ) =
      Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
        A_fine A_coarse (positiveEdgeOfPhysicalBond b)
        (Gamma1 b) (Gamma2 b) (Gamma3 b) := by
  unfold cmp99PhysicalUbarBlockOfDeviationBudget
  dsimp only
  rw [cmp99UbarSpecialUnitaryBlockOfDeviationBudget_coe]
  change NormedSpace.exp
      (∑ x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b)),
        (M ^ d : ℝ)⁻¹ • nearLog
          (((UbarDeviation A_fine A_coarse
            (positiveEdgeOfPhysicalBond b) x
            (Gamma1 b) (Gamma2 b) (Gamma3 b) : SUN Nc) :
              Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) *
        (A_coarse (positiveEdgeOfPhysicalBond b) :
          Matrix (Fin Nc) (Fin Nc) ℂ) =
    NormedSpace.exp
      ((M ^ d : ℝ)⁻¹ •
        ∑ x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
            (positiveEdgeOfPhysicalBond b)),
          nearLog
            (((UbarDeviation A_fine A_coarse
              (positiveEdgeOfPhysicalBond b) x
              (Gamma1 b) (Gamma2 b) (Gamma3 b) : SUN Nc) :
                Matrix (Fin Nc) (Fin Nc) ℂ) - 1)) *
        (A_coarse (positiveEdgeOfPhysicalBond b) :
          Matrix (Fin Nc) (Fin Nc) ℂ)
  apply congrArg (fun Z : Matrix (Fin Nc) (Fin Nc) ℂ =>
    NormedSpace.exp Z *
      (A_coarse (positiveEdgeOfPhysicalBond b) :
        Matrix (Fin Nc) (Fin Nc) ℂ))
  exact (Finset.smul_sum
    (r := (M ^ d : ℝ)⁻¹)
    (s := blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
      (positiveEdgeOfPhysicalBond b)))
    (f := fun x => nearLog
      (((UbarDeviation A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
        (Gamma1 b) (Gamma2 b) (Gamma3 b) : SUN Nc) :
          Matrix (Fin Nc) (Fin Nc) ℂ) - 1))).symm

/-- Gauge covariance of the exact direct-deviation-budget Ubar constructor.
This is the constructor used by `CMP99PhysicalRegionalScaleData.nextBackground`.
The two deviation certificates certify the two definitionally different
constructor calls; they are produced from one transformed small-field witness
at the source endpoint. -/
theorem cmp99PhysicalUbarGaugeConfigOfDeviationBudget_gaugeAct
    (u : GaugeTransform d (M * N') (SUN Nc))
    (A_fine : GaugeConfig d (M * N') (SUN Nc))
    (A_coarse : GaugeConfig d N' (SUN Nc))
    (Gamma1 Gamma2 Gamma3 : PhysicalBond d N' →
      FinBox d (M * N') → List (ConcreteEdge d (M * N')))
    (B : MatrixNearLogNoWindingBudget Nc)
    (hdev : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
          (Gamma1 b) (Gamma2 b) (Gamma3 b)‖ ≤ B.δ)
    (hdevT : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
          (positiveEdgeOfPhysicalBond b) x
          (Gamma1 b) (Gamma2 b) (Gamma3 b)‖ ≤ B.δ)
    (hpath1 : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      IsPathFrom
        (blockBasepoint M N' (FiniteLatticeGeometry.src (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b))) (Gamma1 b x))
    (hend1 : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      pathEnd
        (blockBasepoint M N' (FiniteLatticeGeometry.src (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b))) (Gamma1 b x) = x)
    (hpath2 : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) → IsPathFrom x (Gamma2 b x))
    (hpath3 : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      IsPathFrom (pathEnd x (Gamma2 b x)) (Gamma3 b x))
    (hend3 : ∀ b x,
      x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)) →
      pathEnd (pathEnd x (Gamma2 b x)) (Gamma3 b x) =
        blockBasepoint M N' (FiniteLatticeGeometry.dst (G := SUN Nc)
          (positiveEdgeOfPhysicalBond b))) :
    cmp99PhysicalUbarGaugeConfigOfDeviationBudget
        (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
        Gamma1 Gamma2 Gamma3 B hdevT =
      gaugeAct (coarseTransform u)
        (cmp99PhysicalUbarGaugeConfigOfDeviationBudget
          A_fine A_coarse Gamma1 Gamma2 Gamma3 B hdev) := by
  let AbarT := cmp99PhysicalUbarGaugeConfigOfDeviationBudget
    (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
    Gamma1 Gamma2 Gamma3 B hdevT
  let Abar := cmp99PhysicalUbarGaugeConfigOfDeviationBudget
    A_fine A_coarse Gamma1 Gamma2 Gamma3 B hdev
  have hY (b : PhysicalBond d N') :
      ∀ x ∈ blockOf M N' (FiniteLatticeGeometry.src (G := SUN Nc)
        (positiveEdgeOfPhysicalBond b)),
        ‖UbarDeviationLogArg
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          A_fine A_coarse (positiveEdgeOfPhysicalBond b) x
          (Gamma1 b) (Gamma2 b) (Gamma3 b)‖ < 1 := by
    intro x hx
    exact lt_of_le_of_lt (hdev b x hx) B.δ_lt_one
  have hpos (b : PhysicalBond d N') :
      AbarT (positiveEdgeOfPhysicalBond b) =
        gaugeAct (coarseTransform u) Abar
          (positiveEdgeOfPhysicalBond b) := by
    dsimp [AbarT, Abar]
    rw [cmp99PhysicalUbarGaugeConfigOfDeviationBudget_apply_pos]
    apply Subtype.ext
    rw [cmp99PhysicalUbarBlockOfDeviationBudget_coe_eq_Ubar]
    calc
      Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          (gaugeAct u A_fine) (gaugeAct (coarseTransform u) A_coarse)
          (positiveEdgeOfPhysicalBond b)
          (Gamma1 b) (Gamma2 b) (Gamma3 b) =
        (MatrixRealization.rep
            (u (blockBasepoint M N'
              (FiniteLatticeGeometry.src (G := SUN Nc)
                (positiveEdgeOfPhysicalBond b)))) :
              (Matrix (Fin Nc) (Fin Nc) ℂ)ˣ).val *
          Ubar (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
            A_fine A_coarse (positiveEdgeOfPhysicalBond b)
            (Gamma1 b) (Gamma2 b) (Gamma3 b) *
          (MatrixRealization.rep
            (u (blockBasepoint M N'
              (FiniteLatticeGeometry.dst (G := SUN Nc)
                (positiveEdgeOfPhysicalBond b)))) :
              (Matrix (Fin Nc) (Fin Nc) ℂ)ˣ)⁻¹.val :=
        Ubar_gaugeAct
          (𝔸 := Matrix (Fin Nc) (Fin Nc) ℂ)
          u A_fine A_coarse (positiveEdgeOfPhysicalBond b)
          (Gamma1 b) (Gamma2 b) (Gamma3 b)
          (hpath1 b) (hend1 b) (hpath2 b) (hpath3 b) (hend3 b)
          (hY b)
      _ = (MatrixRealization.rep
          (coarseTransform u
              (FiniteLatticeGeometry.src (G := SUN Nc)
                (positiveEdgeOfPhysicalBond b)) *
            cmp99PhysicalUbarBlockOfDeviationBudget
              A_fine A_coarse Gamma1 Gamma2 Gamma3 B hdev b *
            (coarseTransform u
              (FiniteLatticeGeometry.dst (G := SUN Nc)
                (positiveEdgeOfPhysicalBond b)))⁻¹) :
            (Matrix (Fin Nc) (Fin Nc) ℂ)ˣ).val := by
        simp only [map_mul, map_inv, Units.val_mul, matrixRealizationSUN_val]
        rw [cmp99PhysicalUbarBlockOfDeviationBudget_coe_eq_Ubar]
        rfl
      _ = (coarseTransform u
          (FiniteLatticeGeometry.src (G := SUN Nc)
            (positiveEdgeOfPhysicalBond b)) *
        cmp99PhysicalUbarBlockOfDeviationBudget
          A_fine A_coarse Gamma1 Gamma2 Gamma3 B hdev b *
        (coarseTransform u
          (FiniteLatticeGeometry.dst (G := SUN Nc)
            (positiveEdgeOfPhysicalBond b)))⁻¹ : SUN Nc) :=
        matrixRealizationSUN_val _
  change AbarT = gaugeAct (coarseTransform u) Abar
  apply gaugeConfig_ext
  intro e
  rcases e with ⟨y, mu, sign⟩
  cases sign with
  | true => exact hpos (y, mu)
  | false =>
      let epos := positiveEdgeOfPhysicalBond (y, mu)
      calc
        AbarT (ConcreteEdge.mk y mu false) = (AbarT epos)⁻¹ := by
          simpa [epos, positiveEdgeOfPhysicalBond] using AbarT.map_reverse epos
        _ = (gaugeAct (coarseTransform u) Abar epos)⁻¹ :=
          congrArg Inv.inv (hpos (y, mu))
        _ = gaugeAct (coarseTransform u) Abar
            (ConcreteEdge.mk y mu false) := by
          simpa [epos, positiveEdgeOfPhysicalBond] using
            (gaugeAct (coarseTransform u) Abar).map_reverse epos |>.symm

/-- The straight source coarse background is gauge covariant.  This is a
derived holonomy statement, not an independently supplied coarse field. -/
theorem cmp99SourceBaseCoarseBackground_gaugeAct
    (u : GaugeTransform d (M * N') (SUN Nc))
    (A : GaugeConfig d (M * N') (SUN Nc)) :
    cmp99SourceBaseCoarseBackground (gaugeAct u A) =
      gaugeAct (coarseTransform u) (cmp99SourceBaseCoarseBackground A) := by
  apply gaugeConfig_ext
  have hpos (b : PhysicalBond d N') :
      cmp99SourceBaseCoarseBackground (gaugeAct u A)
          (positiveEdgeOfPhysicalBond b) =
        gaugeAct (coarseTransform u) (cmp99SourceBaseCoarseBackground A)
          (positiveEdgeOfPhysicalBond b) := by
    have hpath :=
      (cmp99SourceParallelTransportPath (G := SUN Nc)
        (blockBasepoint M N' b.1) b.2).holonomy_gaugeAct u A
    have hend :
        cmp99SourceTranslatedSite (blockBasepoint M N' b.1) b.2 =
          blockBasepoint M N' (b.1.shift b.2) := by
      rw [← cmp99BlockEmbed_default b.1,
        cmp99SourceTranslatedSite_blockEmbed,
        cmp99BlockEmbed_default]
    simpa [cmp99SourceBaseCoarseBackground_apply_pos,
      GaugeConfig.gaugeAct_apply, coarseTransform,
      positiveEdgeOfPhysicalBond, ConcreteEdge.srcV, ConcreteEdge.dstV,
      hend] using hpath
  intro e
  rcases e with ⟨y, mu, sign⟩
  cases sign with
  | true =>
      simpa [positiveEdgeOfPhysicalBond] using hpos (y, mu)
  | false =>
      let epos := positiveEdgeOfPhysicalBond (y, mu)
      calc
        cmp99SourceBaseCoarseBackground (gaugeAct u A)
            (ConcreteEdge.mk y mu false) =
            (cmp99SourceBaseCoarseBackground (gaugeAct u A) epos)⁻¹ := by
              simpa [epos, positiveEdgeOfPhysicalBond] using
                (cmp99SourceBaseCoarseBackground (gaugeAct u A)).map_reverse epos
        _ = (gaugeAct (coarseTransform u)
            (cmp99SourceBaseCoarseBackground A) epos)⁻¹ := by
              congr 1
              simpa [epos] using hpos (y, mu)
        _ = gaugeAct (coarseTransform u)
            (cmp99SourceBaseCoarseBackground A)
              (ConcreteEdge.mk y mu false) := by
              simpa [epos, positiveEdgeOfPhysicalBond] using
                (gaugeAct (coarseTransform u)
                  (cmp99SourceBaseCoarseBackground A)).map_reverse epos |>.symm

end

end YangMills.RG
