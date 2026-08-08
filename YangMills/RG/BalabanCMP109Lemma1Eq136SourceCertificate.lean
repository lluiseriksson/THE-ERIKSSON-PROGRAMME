import YangMills.RG.BalabanCMP102Eq80CutoffRadialResidual
import YangMills.RG.BalabanCMP102PhysicalBackgroundZeroChart
import YangMills.RG.BalabanCMP109Lemma1ResidualFamily
import YangMills.RG.BalabanCMP116Eq230TreeMetric
import YangMills.RG.BalabanCMP116PartialResidualAssembly

/-!
# Source-pinned equation-(1.36) certificate for the CMP109 Lemma-1 sector

The generic partial-residual ledger is intentionally reusable, but a terminal
CMP116 producer must not be able to fill its Lemma-1 slot with an arbitrary
function.  This file pins that slot to the literal CMP109 residual activity
from equation (2.12), including the nonlinear correction field supplied as a
function of the fluctuation.

The bound is restricted to the printed small-field ball
`|B| < epsilon1 / gk on Y`.  Here `on Y` is represented literally on the
fluctuation lattice: both endpoints of a retained physical bond belong to
the native block carrier `Y.blocks`.  This is deliberately not the ambient
sup norm.  Its amplitude is strictly positive, and the small-field predicate
contains the zero field.  Thus neither a zero choice for the named Lemma-1
amplitude nor an empty support predicate can inhabit this certificate.  The
outer source constants remain the responsibility of the physical parameter
producer.

Honest scope: the native residual is indexed by connected `2`-block domains
on the one-step finer lattice.  This certificate does not itself install the
final CMP116 domain ledger.  The companion native-family module retains every
such domain as a distinct index and coarsens only its physical support; no
quotient by coincident target supports is part of that construction.
-/

namespace YangMills.RG

noncomputable section

private abbrev Lemma1NativeDomain (M Q : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  CMP116LocalizationDomain 2 (M * (2 * Q))

private abbrev Lemma1FineField (M Q Nc : ℕ)
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] :=
  FinePhysicalOneCochain 4 M (2 * Q) Nc

private abbrev Lemma1CoarseField (Q Nc : ℕ) [NeZero (2 * Q)] :=
  CoarsePhysicalOneCochain 4 (2 * Q) Nc

/-- Physical fluctuation bonds contained bilaterally in a native Lemma-1
domain.  The domain blocks live on `FinBox 4 (M * (2 * Q))`, exactly the site
lattice of the fluctuation field `B`; using `Y.bondSupport` here would insert
an erroneous additional order-two refinement. -/
noncomputable def cmp109Lemma1SourceBondSupport
    {M Q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (Y : Lemma1NativeDomain M Q) :
    Finset (PhysicalBond 4 (M * (2 * Q))) :=
  Finset.univ.filter fun bond =>
    cmp116BondSource bond ∈ Y.blocks ∧ cmp116BondTarget bond ∈ Y.blocks

@[simp] theorem mem_cmp109Lemma1SourceBondSupport_iff
    {M Q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    {Y : Lemma1NativeDomain M Q}
    {bond : PhysicalBond 4 (M * (2 * Q))} :
    bond ∈ cmp109Lemma1SourceBondSupport Y ↔
      cmp116BondSource bond ∈ Y.blocks ∧
        cmp116BondTarget bond ∈ Y.blocks := by
  simp [cmp109Lemma1SourceBondSupport]

/-- The literal small-field domain from CMP116 (1.34): the source sup norm
of the fluctuation restricted to the interior of the individual domain
`Y`.  The primary text says both `on Y` and that the localized function
depends on `B` restricted to the interior of `Y`; it does not impose an
ambient-volume sup-norm bound. -/
def cmp109Lemma1SourceSmallField
    {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))]
    (epsilon1 gk : ℝ)
    (Y : Lemma1NativeDomain M Q)
    (B : Lemma1FineField M Q Nc) : Prop :=
  cmp98SourceFieldSupNorm
      (physicalBondProjection (cmp109Lemma1SourceBondSupport Y) B) ≤
    epsilon1 / gk

/-- The literal CMP109 Lemma-1 residual after installing the correction
field `D(B)`.  No arbitrary residual function occurs in this definition. -/
noncomputable def cmp109Lemma1SourceResidual
    {Index : Type*} {M Q Nc : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] [NeZero Nc]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (gk : ℝ)
    (D : Lemma1FineField M Q Nc → Lemma1CoarseField Q Nc)
    (Y : Lemma1NativeDomain M Q)
    (B : Lemma1FineField M Q Nc) : ℝ :=
  cmp109Eq212Lemma1ResidualActivity E V gk B (D B) Y

/-- Equation-(1.36) as the genuine remaining CMP109 Lemma-1 input.

Unlike the generic ledger certificate, both the residual and the small-field
predicate are fixed by the parameters of this structure. -/
structure CMP109Lemma1Eq136SourceCertificate
    {Index : Type*} {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] [NeZero Nc]
    (E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc)
    (V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc)
    (gk : ℝ)
    (D : Lemma1FineField M Q Nc → Lemma1CoarseField Q Nc)
    (epsilon1 C1 C2 kappa1 delta kappa : ℝ) where
  E0 : ℝ
  E0_pos : 0 < E0
  epsilon1_nonneg : 0 ≤ epsilon1
  gk_pos : 0 < gk
  bound :
    ∀ Y B, cmp109Lemma1SourceSmallField epsilon1 gk Y B →
      |cmp109Lemma1SourceResidual E V gk D Y B| ≤
        cmp116Eq136ResidualMajorant E0 epsilon1 C1 M q
          C2 kappa1 delta kappa
          (cmp116CubeEdgeTreeMetric Y : ℝ)

/-- The source-pinned certificate induces the generic restricted certificate
on the native domain index.  This is not the missing scale reindexing. -/
noncomputable def CMP109Lemma1Eq136SourceCertificate.toNativeCertificate
    {Index : Type*} {M Q Nc q : ℕ}
    [NeZero M] [NeZero Q] [NeZero (2 * Q)]
    [NeZero (M * (2 * Q))] [NeZero Nc]
    {E : CMP109LocalizedActionExpansion Index 2 (M * (2 * Q)) Nc}
    {V : PhysicalGaugeBackground 4 (M * (2 * Q)) Nc}
    {gk : ℝ}
    {D : Lemma1FineField M Q Nc → Lemma1CoarseField Q Nc}
    {epsilon1 C1 C2 kappa1 delta kappa : ℝ}
    (S : CMP109Lemma1Eq136SourceCertificate (q := q)
      E V gk D epsilon1 C1 C2 kappa1 delta kappa) :
    CMP116Lemma1Eq136ResidualCertificate
      (fun Y : Lemma1NativeDomain M Q =>
        (cmp116CubeEdgeTreeMetric Y : ℝ))
      (cmp109Lemma1SourceSmallField epsilon1 gk)
      (cmp109Lemma1SourceResidual E V gk D)
      epsilon1 C1 M q C2 kappa1 delta kappa where
  E0 := S.E0
  E0_pos := S.E0_pos
  smallField_zero := by
    intro Y
    unfold cmp109Lemma1SourceSmallField
    rw [map_zero]
    rw [cmp98SourceFieldSupNorm_zero]
    exact div_nonneg S.epsilon1_nonneg (le_of_lt S.gk_pos)
  bound := S.bound

end

end YangMills.RG
