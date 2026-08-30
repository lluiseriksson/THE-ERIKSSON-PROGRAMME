import YangMills.RG.BalabanCMP89NeumannReflectionRepresentation
import YangMills.RG.FinitePiLpCombesThomas
import YangMills.RG.BalabanCMP89SourceNeumannRegionalGaugePrecision

/-!
# Canonical-inverse gate for the CMP89 Neumann reflection representation

PRE-VALIDATION: source is present, its `.olean` has not been materialized,
and no declaration below is compiler-verified.

The existing CMP89 (2.42) certificate accepts a regional kernel as a
parameter. This source-facing gate removes that freedom: the regional entry
is definitionally the evaluation of one supplied Green operator on a
single-site fibre probe. Proving the gate therefore proves the reflection
formula for that operator, rather than for a kernel chosen to equal the
series.
-/

namespace YangMills.RG

noncomputable section

variable {d N : ℕ} [NeZero d] [NeZero N]
variable {g : Type*}
variable [NormedAddCommGroup g] [InnerProductSpace ℝ g]
variable [FiniteDimensional ℝ g]

/-- The literal operator kernel entry at one fibre vector. -/
def cmp89FinitePiLpGreenEntryAt
    {Omega : ActiveGaugeRegion d N}
    (green : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    (target source : ActiveGaugeRegion.Site Omega)
    (v : g) : g :=
  green (singleFinitePiLp source v) target

/-- Exact CMP89 (2.42) gate for one already constructed regional Green.

`siteEquiv` is the still-open half-open-rectangle dictionary. The full
lattice kernel acts on the same fibre vector; no scalar-to-gauge
identification is hidden in this proposition.
-/
def CMP89CanonicalNeumannReflectionRepresentation
    {Omega : ActiveGaugeRegion d N}
    {m : Fin d → ℤ}
    (siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃
      ActiveGaugeRegion.Site Omega)
    (green : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g)
    (fullGreenAction :
      (Fin d → ℤ) → (Fin d → ℤ) → g → g) : Prop :=
  ∀ v : g,
    CMP89NeumannReflectionRepresentationCertificate m
      (fun x n ↦ cmp89FinitePiLpGreenEntryAt green
        (siteEquiv x) (siteEquiv n) v)
      (fun x y ↦ fullGreenAction x y v)

/-- Projection of the source formula with the canonical regional entry
printed in the conclusion. -/
theorem cmp89CanonicalNeumannReflectionRepresentation_eq_series
    {Omega : ActiveGaugeRegion d N}
    {m : Fin d → ℤ}
    {siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃
      ActiveGaugeRegion.Site Omega}
    {green : ActiveGaugeZeroCochain Omega g →L[ℝ]
      ActiveGaugeZeroCochain Omega g}
    {fullGreenAction :
      (Fin d → ℤ) → (Fin d → ℤ) → g → g}
    (C : CMP89CanonicalNeumannReflectionRepresentation
      siteEquiv green fullGreenAction)
    (v : g) (x n : CMP89SourceNeumannIntegerRectanglePoint m) :
    cmp89FinitePiLpGreenEntryAt green
        (siteEquiv x) (siteEquiv n) v =
      cmp89NeumannReflectionSeries
        (fun y z ↦ fullGreenAction y z v) m x.1 n.1 :=
  (C v).eq_series x n

/-! ## Retained physical specialization -/

variable {Nc M depth : ℕ} [NeZero Nc] [NeZero M]
variable {Omega : ActiveGaugeRegion d N}
variable {rho : SUNAdjointModel Nc} {spacing : ℝ}
variable {background : GaugeConfig d N (SUN Nc)}

/-- Source-facing CMP89 (2.42) gate with no free regional Green.

The regional kernel is definitionally the canonical inverse of the literal
three-term retained Neumann precision. The rectangle equivalence and the
full-lattice Green action remain the two source dictionaries still visible in
the signature. -/
def CMP89SourceRetainedCanonicalNeumannReflectionRepresentation
    {m : Fin d → ℤ}
    (T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth)
    (r : CMP85PositivePrefix depth)
    (mass : ℝ) {a CP : ℝ}
    (ha : 0 < a) (hspacing : 0 < spacing) (hCP : 0 < CP)
    (hP : CMP89SourceRetainedNeumannPrefixPoincare T r CP)
    (siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃
      ActiveGaugeRegion.Site Omega)
    (fullGreenAction :
      (Fin d → ℤ) → (Fin d → ℤ) → SUNLieCoord Nc → SUNLieCoord Nc) :
    Prop :=
  CMP89CanonicalNeumannReflectionRepresentation
    (d := d) (N := N) (g := SUNLieCoord Nc)
    (Omega := Omega) (m := m) siteEquiv
    (cmp89SourceRetainedNeumannPrefixGreen
      (d := d) (N := N) (Nc := Nc) (M := M) (depth := depth)
      (Omega := Omega) (rho := rho) (spacing := spacing)
      (background := background)
      T r mass ha hspacing hCP hP)
    fullGreenAction

/-- Projection of the retained physical formula with the regional entry
fixed to the canonical inverse constructed from the same tower and Poincare
gate. -/
theorem cmp89SourceRetainedCanonicalNeumannReflectionRepresentation_eq_series
    {m : Fin d → ℤ}
    {T : CMP99SourceRetainedPhysicalTower
      rho Omega M spacing background depth}
    {r : CMP85PositivePrefix depth}
    {mass : ℝ} {a CP : ℝ}
    {ha : 0 < a} {hspacing : 0 < spacing} {hCP : 0 < CP}
    {hP : CMP89SourceRetainedNeumannPrefixPoincare T r CP}
    {siteEquiv : CMP89SourceNeumannIntegerRectanglePoint m ≃
      ActiveGaugeRegion.Site Omega}
    {fullGreenAction :
      (Fin d → ℤ) → (Fin d → ℤ) → SUNLieCoord Nc → SUNLieCoord Nc}
    (C : CMP89SourceRetainedCanonicalNeumannReflectionRepresentation
      T r mass ha hspacing hCP hP siteEquiv fullGreenAction)
    (v : SUNLieCoord Nc)
    (x n : CMP89SourceNeumannIntegerRectanglePoint m) :
    cmp89FinitePiLpGreenEntryAt
        (d := d) (N := N) (g := SUNLieCoord Nc) (Omega := Omega)
        (cmp89SourceRetainedNeumannPrefixGreen
          (d := d) (N := N) (Nc := Nc) (M := M) (depth := depth)
          (Omega := Omega) (rho := rho) (spacing := spacing)
          (background := background)
          T r mass ha hspacing hCP hP)
        (siteEquiv x) (siteEquiv n) v =
      cmp89NeumannReflectionSeries
        (fun y z ↦ fullGreenAction y z v) m x.1 n.1 :=
  cmp89CanonicalNeumannReflectionRepresentation_eq_series
    (d := d) (N := N) (g := SUNLieCoord Nc)
    (Omega := Omega) (m := m) (siteEquiv := siteEquiv)
    (green := cmp89SourceRetainedNeumannPrefixGreen
      (d := d) (N := N) (Nc := Nc) (M := M) (depth := depth)
      (Omega := Omega) (rho := rho) (spacing := spacing)
      (background := background)
      T r mass ha hspacing hCP hP)
    (fullGreenAction := fullGreenAction) C v x n

end

end YangMills.RG
