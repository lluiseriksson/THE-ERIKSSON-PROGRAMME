import YangMills.RG.BalabanCMP99SourceGeneratedFlatPhysicalPointSourceOuterSynthesisDictionary
import YangMills.RG.BalabanCMP99SourceFlatFullPointSourcePhysicalEndpointReflection
import YangMills.RG.BalabanCMP99SourceFlatFullPointSourceReversedOwnerCharacter
import YangMills.RG.BalabanCMP99FullGreenPhysicalFiniteGridAliasing

/-!
# PRE-VALIDATION: generated point-source Green as one affine residue-class sum

This is route step 10.  It composes the cold-sealed outer
synthesis, endpoint reflection and character dictionaries with the literal
physical finite-grid aliasing theorem.  The fine-block normalization
`Kfine⁻⁴` remains visible; it is not absorbed into a constant.

This finite identity does not prove CMP89 (2.42), produce uniform physical
`B0`/`delta0`, attain window 15, discharge a terminal field, move `20/41`,
or construct a `TermSource`.
-/

namespace YangMills.RG

open scoped BigOperators

noncomputable section

/-- The literal affine residue-class coefficient selected by the two
fine-site owners. Naming this scalar keeps the physical theorem signature
small while preserving the displayed `K⁻⁴` normalization and every endpoint
displacement definitionally. -/
def cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum
    {M Q : ℕ} [NeZero M] [NeZero Q] (depth : ℕ) (a : ℝ)
    (source target : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q)))) : ℂ :=
  let K : ℕ := M ^ (depth + 1)
  let N : ℕ := 2 * (M * Q)
  letI : NeZero K := by
    dsimp [K]
    infer_instance
  letI : NeZero N := by
    dsimp [N]
    infer_instance
  (((K : ℂ) ^ 4)⁻¹) *
    (∑' n : CMP99FlatIntegerResidueClass 4 N
        (cmp99FinBoxZModEquiv 4 N (blockSite K N source) -
          cmp99FinBoxZModEquiv 4 N (blockSite K N target)),
      cmp89Eq246CenteredFullGreenPhysicalFourierCoefficient
        K 1 0 a
        (fun mu =>
          -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
            K source (blockSite K N source) mu)
        (fun mu =>
          -cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
            K target (blockSite K N target) mu)
        n)

/-- The generated physical point-source Green evaluated at one target and one
matrix coordinate. Naming this scalar prevents the terminal identity from
re-elaborating the complete specialized operator in its theorem header. -/
def cmp99SourceGeneratedFlatPhysicalPointSourceGreenValue
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    (hM : 2 ≤ M) (depth : ℕ)
    (source target : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q))))
    (v : SUNLieComplexCoord Nc) (A : Fin (Nc ^ 2 - 1)) : ℂ :=
  (cmp99SourceGeneratedFlatPhysicalStep7bGreenCLM
      (M := M) (Q := Q) (Nc := Nc) hM depth
      (cmp99FlatComplexFibrePointSource source v)) target A

/-- The complete source and analytic-window data consumed by the physical
residue-class identity. Every former theorem argument remains a visible field;
the record only prevents the elaborator from normalizing one long dependent
Pi-header at once. -/
structure CMP99SourceGeneratedFlatPhysicalPointSourceResidueClassData
    (M Q Nc : ℕ) [NeZero M] [NeZero Q] [NeZero Nc] where
  hM : 2 ≤ M
  depth : ℕ
  rho : ℝ
  hrho : 0 < rho
  hamplitude : rho * Real.exp rho ≤ 1 / 6
  hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho
  hdenWindow : CMP89Eq249CentralStabilizedComplexWindow
    (cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0) rho
  hpairWindow : CMP89Eq249CentralAveragePairComplexWindow rho
  source : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q)))
  target : FinBox 4 (M ^ (depth + 1) * (2 * (M * Q)))
  v : SUNLieComplexCoord Nc
  A : Fin (Nc ^ 2 - 1)

/-- A proposition-valued certificate whose field is the exact physical
residue-class equality. Unlike a reducible `Prop` definition, the structure
type lets the terminal theorem remain opaque during header elaboration while
the named projection exposes the literal equality to consumers. -/
structure CMP99SourceGeneratedFlatPhysicalPointSourceResidueClassCertificate
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    (data : CMP99SourceGeneratedFlatPhysicalPointSourceResidueClassData M Q Nc) : Prop where
  eq_scaledResidueClass :
    cmp99SourceGeneratedFlatPhysicalPointSourceGreenValue
      (M := M) (Q := Q) (Nc := Nc) data.hM data.depth
      data.source data.target data.v data.A =
      cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum
        (M := M) (Q := Q) data.depth
        (cmp99SourceGeneratedFullComplexA 4 M (data.depth + 1)
          (cmp99SourceGeneratedFullComplexSpacing M (data.depth + 1)) 0)
        data.source data.target * data.v data.A

/-- The generated full periodic point-source Green is the affine residue
sum selected by the reversed endpoint-owner difference, with the remaining
fine-block normalization shown literally. -/
theorem cmp99SourceGeneratedFlatPhysicalPointSourceGreen_apply_eq_scaledResidueClass
    {M Q Nc : ℕ} [NeZero M] [NeZero Q] [NeZero Nc]
    (data : CMP99SourceGeneratedFlatPhysicalPointSourceResidueClassData M Q Nc) :
    CMP99SourceGeneratedFlatPhysicalPointSourceResidueClassCertificate data := by
  constructor
  rcases data with
    ⟨hM, depth, rho, hrho, hamplitude, hradius, hdenWindow, hpairWindow,
      source, target, v, A⟩
  let Kfine : ℕ := M ^ (depth + 1)
  let N : ℕ := 2 * (M * Q)
  let a : ℝ :=
    cmp99SourceGeneratedFullComplexA 4 M (depth + 1)
      (cmp99SourceGeneratedFullComplexSpacing M (depth + 1)) 0
  let targetOwner : FinBox 4 N := blockSite Kfine N target
  let sourceOwner : FinBox 4 N := blockSite Kfine N source
  let targetDisp : Fin 4 → ℤ := fun mu =>
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
      Kfine target targetOwner mu
  let sourceDisp : Fin 4 → ℤ := fun mu =>
    cmp99SourceFlatQprimeFineToCoarseEndpointDisplacement
      Kfine source sourceOwner mu
  let r : CMP99FlatZModBox 4 N :=
    cmp99FinBoxZModEquiv 4 N sourceOwner -
      cmp99FinBoxZModEquiv 4 N targetOwner
  letI : NeZero Kfine := by
    dsimp [Kfine]
    infer_instance
  letI : NeZero N := by
    dsimp [N]
    infer_instance
  have ha : 0 < a := by
    simpa [a] using cmp99SourceGeneratedFullComplexA_pos_physical M depth
  have hreflect : ∀ ell : FinBox 4 N,
      cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
          (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (fun mu => -targetDisp mu) (fun mu => -sourceDisp mu) =
        cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
          (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu) := by
    intro ell
    exact cmp99SourceFlatFullPointSourcePhysicalFineToFineGreenIntegrand_neg_swap
      ha hrho.le hamplitude hradius hdenWindow hpairWindow
      ell targetDisp sourceDisp
  have hchar : ∀ ell : FinBox 4 N,
      cmp99FlatFourierMode ell targetOwner *
          (cmp99FlatFourierMode ell sourceOwner)⁻¹ =
        cmp99FlatZModFourierCharacter
          (-(cmp99FinBoxZModEquiv 4 N ell)) r := by
    intro ell
    simpa [r] using
      cmp99FlatFourierMode_target_mul_source_inv_eq_reversedOwnerDifferenceCharacter
        ell targetOwner sourceOwner
  have hphysical : ∀ ell : FinBox 4 N,
      cmp89Eq246StabilizedFineToFineGreenIntegrand 4 Kfine 1 0 a
          (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (cmp89Eq249PhysicalFineLatticeDisplacement ((Kfine : ℝ)⁻¹)
            (fun mu => -targetDisp mu))
          (cmp89Eq249PhysicalFineLatticeDisplacement ((Kfine : ℝ)⁻¹)
            (fun mu => -sourceDisp mu)) =
        cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
          (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
          (fun mu => -targetDisp mu) (fun mu => -sourceDisp mu) := by
    intro ell
    simpa [cmp89Eq249FineLatticeSpacing] using
      (cmp89Eq246PhysicalFineToFineGreenIntegrand_eq Kfine 1 0 a
        (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (fun mu => -targetDisp mu) (fun mu => -sourceDisp mu)).symm
  let endpoint : FinBox 4 N → ℂ := fun ell =>
    cmp99FlatZModFourierCharacter
        (-(cmp99FinBoxZModEquiv 4 N ell)) r *
      cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
        (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
        (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu)
  have hbox :
      (∑ ell : FinBox 4 N, endpoint ell) =
        ∑ k : CMP99FlatZModBox 4 N,
          cmp99FlatZModFourierCharacter (-k) r *
            cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
              (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
                ((cmp99FinBoxZModEquiv 4 N).symm k))
              (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu) := by
    simpa [endpoint] using
      (Equiv.sum_comp (cmp99FinBoxZModEquiv 4 N)
        (fun k : CMP99FlatZModBox 4 N =>
          cmp99FlatZModFourierCharacter (-k) r *
            cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
              (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
                ((cmp99FinBoxZModEquiv 4 N).symm k))
              (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu)))
  have halias :=
    cmp99Flat_normalizedFiniteGridFullPhysicalGreenSample_eq_residueClass
      (K := Kfine) (N := N) (a := a) (rho := rho)
      ha hrho hamplitude hradius hdenWindow hpairWindow
      (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu) r
  unfold cmp99SourceGeneratedFlatPhysicalPointSourceGreenValue
  rw [cmp99SourceGeneratedFlatPhysicalPointSourceGreen_apply_eq_outerIntegrandSum
    (M := M) (Q := Q) (Nc := Nc) hM depth source target v A]
  dsimp only [Kfine, N, a, targetOwner, sourceOwner, targetDisp, sourceDisp]
    at hphysical
  simp_rw [hphysical]
  have hterm : ∀ ell : FinBox 4 N,
      ((((((Kfine * N : ℕ) : ℂ) ^ 4)⁻¹) *
            cmp99FlatFourierMode ell targetOwner *
            (cmp99FlatFourierMode ell sourceOwner)⁻¹) *
          cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
            (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
            (fun mu => -targetDisp mu) (fun mu => -sourceDisp mu)) * v A =
        ((((((Kfine * N : ℕ) : ℂ) ^ 4)⁻¹) * endpoint ell) * v A) := by
    intro ell
    calc
      _ = ((((((Kfine * N : ℕ) : ℂ) ^ 4)⁻¹) *
            ((cmp99FlatFourierMode ell targetOwner *
              (cmp99FlatFourierMode ell sourceOwner)⁻¹) *
              cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
                (-cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
                (fun mu => -targetDisp mu) (fun mu => -sourceDisp mu))) * v A) := by
          ring
      _ = ((((((Kfine * N : ℕ) : ℂ) ^ 4)⁻¹) *
            (cmp99FlatZModFourierCharacter
                (-(cmp99FinBoxZModEquiv 4 N ell)) r *
              cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
                (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum ell)
                (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu))) * v A) := by
          rw [hchar ell, hreflect ell]
      _ = _ := by rfl
  dsimp only [Kfine, N, a, targetOwner, sourceOwner, targetDisp, sourceDisp]
    at hterm
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hbox]
  have hscale : ((((Kfine * N : ℕ) : ℂ) ^ 4)⁻¹) =
      (((Kfine : ℂ) ^ 4)⁻¹) * (((N : ℂ) ^ 4)⁻¹) := by
    push_cast
    rw [mul_pow, mul_inv_rev]
    ring
  rw [hscale]
  calc
    _ = (((Kfine : ℂ) ^ 4)⁻¹) *
          ((((N : ℂ) ^ 4)⁻¹) *
            ∑ k : CMP99FlatZModBox 4 N,
              cmp99FlatZModFourierCharacter (-k) r *
                cmp89Eq246PhysicalFineToFineGreenIntegrand Kfine 1 0 a
                  (cmp99SourceFlatQprimeCoarseAmplitudeBaseMomentum
                    ((cmp99FinBoxZModEquiv 4 N).symm k))
                  (fun mu => -sourceDisp mu) (fun mu => -targetDisp mu)) * v A := by
            ring
    _ = _ := by
      rw [halias]
      unfold cmp99SourceGeneratedFlatPhysicalPointSourceResidueClassSum
      dsimp [Kfine, N, a, targetOwner, sourceOwner, targetDisp, sourceDisp, r]

end

end YangMills.RG
