/- STATIC DRAFT ONLY -- NOT COMPILER-VERIFIED.

H4d: transport the internally selected nearest physical endpoint from the
literal signed fine-lattice `l1` metric to the minimum of the two CMP99 owner
distances.  Both endpoint lifts are treated separately before the minimum is
taken.  No target-only replacement, sum of endpoint estimates, regional B0,
window-15 claim or terminal field is asserted here.
-/

import YangMills.RG.BalabanCMP89Eq249NearestCompleteHolderNormalizedBound
import YangMills.RG.BalabanCMP99SourceLocalizationOwnerDistanceBridge

namespace YangMills.RG

noncomputable section

/-- A shortest periodic representative is no longer than any integer lift of
the same coordinate difference. -/
theorem finTorusDist_le_natAbs_of_intCast_eq_sub_draft
    {N : ℕ} [NeZero N] (target source : Fin N) (w : ℤ)
    (hw : (w : ZMod N) =
      (target.val : ZMod N) - (source.val : ZMod N)) :
    finTorusDist target source ≤ w.natAbs := by
  let z : ZMod N :=
    (target.val : ZMod N) - (source.val : ZMod N)
  have hminimal : z.valMinAbs.natAbs ≤ w.natAbs := by
    exact ZMod.natAbs_min_of_le_div_two N z.valMinAbs w
      (by simpa [z] using hw.symm) (ZMod.natAbs_valMinAbs_le z)
  simpa [finTorusDist, zmodCircDist,
    natAbs_valMinAbs_eq_zmodCircVal] using hminimal

/-- Any integer lift of a periodic site difference dominates the literal
fine-site Chebyshev distance.  This is the interface needed by H5 residue
lifts `u + M*n`; centered representatives are only one specialization. -/
theorem finBoxDist_le_latticeL1_of_intCast_eq_siteSub_draft
    {d N : ℕ} [NeZero N] (target source : FinBox d N)
    (u : Fin d → ℤ)
    (hu : ∀ mu, (u mu : ZMod N) =
      ((target mu).val : ZMod N) - (source mu).val) :
    (finBoxDist target source : ℝ) ≤ cmp89Eq251LatticeL1Length u := by
  have hbox := finBoxDist_le_sum_finTorusDist target source
  calc
    (finBoxDist target source : ℝ) ≤
        ∑ mu, (finTorusDist (target mu) (source mu) : ℝ) := by
      exact_mod_cast hbox
    _ ≤ ∑ mu, (((u mu).natAbs : ℕ) : ℝ) := by
      gcongr with mu
      exact_mod_cast
        (finTorusDist_le_natAbs_of_intCast_eq_sub_draft
          (target mu) (source mu) (u mu) (hu mu))
    _ = cmp89Eq251LatticeL1Length u := by rfl

/-- The seam-safe integer lift of the first endpoint dominates the literal
fine-site Chebyshev distance from the physical source to `y`. -/
theorem finBoxDist_le_cmp116CMP89PhysicalBondFirstEndpointDisplacement_realL1_draft
    {N : ℕ} [NeZero N] (b : PhysicalBond 4 N) (y : FinBox 4 N) :
    (finBoxDist (cmp116BondSource b) y : ℝ) ≤
      cmp89Eq251LatticeL1Length
        (cmp116CMP89PhysicalBondFirstEndpointDisplacement b y) := by
  exact finBoxDist_le_latticeL1_of_intCast_eq_siteSub_draft
    (cmp116BondSource b) y
    (cmp116CMP89PhysicalBondFirstEndpointDisplacement b y)
    (cmp116CMP89PhysicalBondFirstEndpointDisplacement_cast b y)

/-- The actual two-point owner metric consumed after the nearest-endpoint
choice.  Its two entries remain literal and separately auditable. -/
def cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q] (depth : ℕ)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) : ℕ :=
  min
    (finBoxDist
      (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondTarget b))
      (cmp99Eq389SourceLocalizationOwner L K Q depth y))
    (finBoxDist
      (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondSource b))
      (cmp99Eq389SourceLocalizationOwner L K Q depth y))

/-- The selected signed-contour length of any correctly projecting integer
lift controls the minimum of the two owner distances.  This is the residue-
stable H4d statement needed by H5. -/
theorem
    cmp116CMP89PhysicalNearestEndpointOwner_mul_dist_le_selectedL1_add_boundary_of_cast_draft
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q] (depth : ℕ)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (transportU : Fin 4 → ℤ)
    (htransportCast : ∀ mu,
      (transportU mu : ZMod
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) =
        ((cmp116BondTarget b mu).val : ZMod
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) -
        (y mu).val) :
    (L ^ (depth + 1) : ℝ) *
        (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft depth b y : ℝ) ≤
      cmp89Eq251LatticeL1Length
          (cmp89Eq249NearestEndpointTransport_draft
            (cmp116CMP89PhysicalBondHolderDisplacement b)
            transportU) +
        (2 * (L ^ (depth + 1) - 1) : ℕ) := by
  let holder := cmp116CMP89PhysicalBondHolderDisplacement b
  let transport := transportU
  let first : Fin 4 → ℤ := fun mu => holder mu + transport mu
  let targetDist : ℝ :=
    finBoxDist
      (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondTarget b))
      (cmp99Eq389SourceLocalizationOwner L K Q depth y)
  let sourceDist : ℝ :=
    finBoxDist
      (cmp99Eq389SourceLocalizationOwner L K Q depth (cmp116BondSource b))
      (cmp99Eq389SourceLocalizationOwner L K Q depth y)
  let boundary : ℝ := (2 * (L ^ (depth + 1) - 1) : ℕ)
  have htarget0 :=
    cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary
      depth (cmp116BondTarget b) y
  have htargetFine :
      (L ^ (depth + 1) : ℝ) * targetDist ≤
        (finBoxDist (cmp116BondTarget b) y : ℝ) + boundary := by
    exact_mod_cast htarget0
  have htarget :
      (L ^ (depth + 1) : ℝ) * targetDist ≤
        cmp89Eq251LatticeL1Length transport + boundary := by
    exact htargetFine.trans (add_le_add_right
      (finBoxDist_le_latticeL1_of_intCast_eq_siteSub_draft
        (cmp116BondTarget b) y transport htransportCast) boundary)
  have hsource0 :=
    cmp99Eq389SourceLocalizationOwner_mul_dist_le_fineDist_add_boundary
      depth (cmp116BondSource b) y
  have hsourceFine :
      (L ^ (depth + 1) : ℝ) * sourceDist ≤
        (finBoxDist (cmp116BondSource b) y : ℝ) + boundary := by
    exact_mod_cast hsource0
  have hsource :
      (L ^ (depth + 1) : ℝ) * sourceDist ≤
        cmp89Eq251LatticeL1Length first + boundary := by
    have hfirstCast : ∀ mu,
        (first mu : ZMod
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) =
          ((cmp116BondSource b mu).val : ZMod
            (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) -
          (y mu).val := by
      intro mu
      dsimp [first, holder, transport]
      rw [Int.cast_add,
        cmp116CMP89PhysicalBondHolderDisplacement_cast, htransportCast]
      ring
    exact hsourceFine.trans (add_le_add_right
      (finBoxDist_le_latticeL1_of_intCast_eq_siteSub_draft
        (cmp116BondSource b) y first hfirstCast) boundary)
  by_cases hnear : cmp89Eq249NearestEndpointUsesTransport_draft holder transport
  · calc
      (L ^ (depth + 1) : ℝ) *
          (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft depth b y : ℝ) ≤
        (L ^ (depth + 1) : ℝ) * targetDist := by
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast min_le_left
          · positivity
      _ ≤ cmp89Eq251LatticeL1Length transport + boundary := htarget
      _ = cmp89Eq251LatticeL1Length
          (cmp89Eq249NearestEndpointTransport_draft holder transport) +
            boundary := by
              simp [cmp89Eq249NearestEndpointTransport_draft, hnear]
  · calc
      (L ^ (depth + 1) : ℝ) *
          (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft depth b y : ℝ) ≤
        (L ^ (depth + 1) : ℝ) * sourceDist := by
          apply mul_le_mul_of_nonneg_left
          · exact_mod_cast min_le_right
          · positivity
      _ ≤ cmp89Eq251LatticeL1Length first + boundary := hsource
      _ = cmp89Eq251LatticeL1Length
          (cmp89Eq249NearestEndpointTransport_draft holder transport) +
            boundary := by
              simp [cmp89Eq249NearestEndpointTransport_draft,
                cmp89Eq249HolderFirstEndpointDisplacement_draft,
                holder, transport, first, hnear]

/-- Centered physical specialization of the residue-stable owner dictionary. -/
theorem
    cmp116CMP89PhysicalNearestEndpointOwner_mul_dist_le_selectedL1_add_boundary_draft
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q] (depth : ℕ)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    (L ^ (depth + 1) : ℝ) *
        (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft depth b y : ℝ) ≤
      cmp89Eq251LatticeL1Length
          (cmp89Eq249NearestEndpointTransport_draft
            (cmp116CMP89PhysicalBondHolderDisplacement b)
            (cmp116CMP89PhysicalBondTransportDisplacement b y)) +
        (2 * (L ^ (depth + 1) - 1) : ℕ) := by
  exact
    cmp116CMP89PhysicalNearestEndpointOwner_mul_dist_le_selectedL1_add_boundary_of_cast_draft
      depth b y (cmp116CMP89PhysicalBondTransportDisplacement b y)
      (cmp116CMP89PhysicalBondTransportDisplacement_cast b y)

/-- Exponentiated residue-stable H4d dictionary. -/
theorem cmp116CMP89PhysicalNearestEndpointWeight_le_ownerWeight_of_cast_draft
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q] (depth : ℕ)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (transportU : Fin 4 → ℤ)
    (htransportCast : ∀ mu,
      (transportU mu : ZMod
        (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) =
        ((cmp116BondTarget b mu).val : ZMod
          (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) -
        (y mu).val) :
    let xi := cmp89Eq249FineLatticeSpacing L (depth + 1)
    let selected := cmp89Eq249NearestEndpointTransport_draft
      (cmp116CMP89PhysicalBondHolderDisplacement b)
      transportU
    Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement xi selected))) ≤
      Real.exp ((rho * xi) * (2 * (L ^ (depth + 1) - 1) : ℕ)) *
        Real.exp (-rho *
          (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
            depth b y : ℝ)) := by
  dsimp only
  let xi := cmp89Eq249FineLatticeSpacing L (depth + 1)
  let rate := rho * xi
  let selected := cmp89Eq249NearestEndpointTransport_draft
    (cmp116CMP89PhysicalBondHolderDisplacement b)
    transportU
  let ownerDist : ℝ :=
    cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft depth b y
  let boundary : ℝ := (2 * (L ^ (depth + 1) - 1) : ℕ)
  have hxi := (cmp89Eq249FineLatticeSpacing_pos L (depth + 1)).le
  have hrate : 0 ≤ rate := mul_nonneg hrho hxi
  have hscale : rate * (L ^ (depth + 1) : ℝ) = rho := by
    have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
    have hpow : (L : ℝ) ^ (depth + 1) ≠ 0 := pow_ne_zero _ hL
    dsimp [rate, xi, cmp89Eq249FineLatticeSpacing]
    rw [Nat.cast_pow, mul_assoc, inv_mul_cancel₀ hpow, mul_one]
  have hmetric :=
    cmp116CMP89PhysicalNearestEndpointOwner_mul_dist_le_selectedL1_add_boundary_of_cast_draft
      depth b y transportU htransportCast
  have hmul := mul_le_mul_of_nonneg_left hmetric hrate
  have hexponent :
      -(rate * cmp89Eq251LatticeL1Length selected) ≤
        rate * boundary - rho * ownerDist := by
    dsimp [selected, ownerDist, boundary] at hmul ⊢
    rw [← hscale]
    nlinarith
  rw [cmp89Eq251DisplacementL1_physicalFineLatticeDisplacement hxi]
  calc
    Real.exp (-(rho * (xi * cmp89Eq251LatticeL1Length selected))) =
        Real.exp (-(rate * cmp89Eq251LatticeL1Length selected)) := by
          congr 2
          dsimp [rate]
          ring
    _ ≤ Real.exp (rate * boundary - rho * ownerDist) :=
      Real.exp_le_exp.mpr hexponent
    _ = Real.exp (rate * boundary) * Real.exp (-rho * ownerDist) := by
      rw [sub_eq_add_neg, Real.exp_add]

/-- Exponentiated H4d dictionary at physical spacing.  The selected endpoint
costs one owner decay and the exact two-corner boundary factor, with no sum of
endpoint weights. -/
theorem cmp116CMP89PhysicalNearestEndpointWeight_le_ownerWeight_draft
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q] (depth : ℕ)
    {rho : ℝ} (hrho : 0 ≤ rho)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    let transportU := cmp116CMP89PhysicalBondTransportDisplacement b y
    let xi := cmp89Eq249FineLatticeSpacing L (depth + 1)
    let selected := cmp89Eq249NearestEndpointTransport_draft
      (cmp116CMP89PhysicalBondHolderDisplacement b) transportU
    Real.exp (-(rho * cmp89Eq251DisplacementL1
        (cmp89Eq249PhysicalFineLatticeDisplacement xi selected))) ≤
      Real.exp ((rho * xi) * (2 * (L ^ (depth + 1) - 1) : ℕ)) *
        Real.exp (-rho *
          (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
            depth b y : ℝ)) := by
  dsimp only
  exact
    cmp116CMP89PhysicalNearestEndpointWeight_le_ownerWeight_of_cast_draft
      depth hrho b y (cmp116CMP89PhysicalBondTransportDisplacement b y)
      (cmp116CMP89PhysicalBondTransportDisplacement_cast b y)

/-- H4d endpoint: the complete Holder integral is controlled by one selected
two-point owner decay.  The exact H2d amplitude and boundary cost remain
visible; regional B0 and window 15 remain open. -/
theorem
    norm_cmp116CMP89PhysicalNearestCompleteHolderIntegral_le_owner_draft
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q] (depth : ℕ)
    {mass a rho alpha : ℝ}
    (ha : 0 ≤ a) (halpha0 : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (halphaStrict : alpha < 1) (hrho : 0 ≤ rho)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6) (mu : Fin 4)
    (b : PhysicalBond 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q)))
    (y : FinBox 4
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q))) :
    let xi := cmp89Eq249FineLatticeSpacing L (depth + 1)
    ‖cmp89Eq249NormalizedFourDimensionalBrillouinIntegral
        (fun x => cmp89Eq251ComplexStabilizedIntegrand 4 L (depth + 1)
          mass a alpha
          (fun nu => (cmp89Eq251PhysicalBrillouinParameter x nu : ℂ)) mu
          (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (cmp116CMP89PhysicalBondHolderDisplacement b))
          (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (cmp116CMP89PhysicalBondTransportDisplacement b y)))‖ ≤
      (Real.exp ((rho * xi) *
          (2 * (L ^ (depth + 1) - 1) : ℕ)) *
        cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft
          a rho alpha) *
        Real.exp (-rho *
          (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
            depth b y : ℝ)) := by
  dsimp only
  let holder := cmp116CMP89PhysicalBondHolderDisplacement b
  let transport := cmp116CMP89PhysicalBondTransportDisplacement b y
  let selected := cmp89Eq249NearestEndpointTransport_draft holder transport
  let xi := cmp89Eq249FineLatticeSpacing L (depth + 1)
  let majorant :=
    cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft a rho alpha
  have hselected :=
    norm_cmp89Eq249NormalizedCompleteHolderIntegral_le_nearestSignedL1_draft
      (L := L) (j := depth + 1) (mass := mass) (a := a) (rho := rho)
      (alpha := alpha) ha halpha0 halpha1 halphaStrict hrho hradius hmass
      hwindow hamplitude mu
      (holder := holder) (transport := transport)
      (cmp116CMP89PhysicalBondHolderDisplacement_unit b)
  have hweight :=
    cmp116CMP89PhysicalNearestEndpointWeight_le_ownerWeight_draft
      depth hrho b y
  have hmajorant : 0 ≤ majorant := by
    dsimp [majorant, cmp89Eq249ComplexPhysicalFineHolderStabilizedBound_draft]
    positivity
  exact hselected.trans <| by
    calc
      Real.exp (-(rho * cmp89Eq251DisplacementL1
          (cmp89Eq249PhysicalFineLatticeDisplacement xi selected))) * majorant ≤
        (Real.exp ((rho * xi) *
            (2 * (L ^ (depth + 1) - 1) : ℕ)) *
          Real.exp (-rho *
            (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
              depth b y : ℝ))) * majorant :=
            mul_le_mul_of_nonneg_right hweight hmajorant
      _ = (Real.exp ((rho * xi) *
            (2 * (L ^ (depth + 1) - 1) : ℕ)) * majorant) *
          Real.exp (-rho *
            (cmp116CMP89PhysicalNearestEndpointOwnerDistance_draft
              depth b y : ℝ)) := by ring

end

end YangMills.RG
