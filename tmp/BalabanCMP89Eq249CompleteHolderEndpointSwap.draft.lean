/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP89Eq251ComplexContourPhase
import YangMills.RG.BalabanCMP89Eq251StabilizedEndpointRecombination

/-!
# PRE-VALIDATION: complete CMP89 Holder endpoint swap

This source is present only as a static draft.  Its `.olean` has not been
materialized and none of the declarations below has been compiler-verified.

CMP89 (2.49) chooses the endpoint nearer to `y` before moving the complete
Holder integrand.  The signed coordinate contour constructed in this branch
naturally measures integer displacements with `cmp89Eq251LatticeL1Length`.
The identification of that length with the source's printed `|x-y|`/`dist`
notation is deliberately left to a separate metric dictionary: the primary
pages 585--586 state the nearest-endpoint convention but do not themselves
fix that norm convention.  If the endpoint selected by the signed `l1`
contour is `x` rather than `x'`, the normalized difference must first be
exchanged exactly.  This module proves the required algebra at the level of
the literal stabilized integrand: with
`h = x-x'` and `t = x'-y`, exchanging the endpoints sends
`(h,t)` to `(-h,h+t)` and negates the complete integrand.

No source-metric identification, endpoint bound, contour equality, local
Holder seminorm, regional `B0`, window-15 attainment, terminal field or
`TermSource` is accepted or produced here.
-/

namespace YangMills.RG

noncomputable section

/-- Negating the Holder displacement preserves its literal Euclidean norm. -/
theorem cmp89Eq251EuclideanNorm_neg_draft
    {d : ℕ} (v : Fin d → ℝ) :
    cmp89Eq251EuclideanNorm (fun mu ↦ -v mu) =
      cmp89Eq251EuclideanNorm v := by
  simp [cmp89Eq251EuclideanNorm, cmp89Eq251MomentumSquare]

/-- A single reciprocal-alias branch is orientation-odd under the exact
endpoint exchange `(h,t) -> (-h,h+t)`. -/
theorem cmp89Eq251ComplexBareAliasNumerator_swap_draft
    {d L j : ℕ} {alpha : ℝ} (z : Fin d → ℂ) (m : Fin d → ℤ)
    (mu : Fin d) (holder transport : Fin d → ℝ) :
    cmp89Eq251ComplexBareAliasNumerator d L j alpha z m mu
        (fun nu ↦ -holder nu) (fun nu ↦ holder nu + transport nu) =
      -cmp89Eq251ComplexBareAliasNumerator d L j alpha z m mu
        holder transport := by
  have hcancel :
      (fun nu ↦ -holder nu + (holder nu + transport nu)) = transport := by
    funext nu
    ring
  rw [cmp89Eq251ComplexBareAliasNumerator_eq_phaseDifference,
    cmp89Eq251ComplexBareAliasNumerator_eq_phaseDifference,
    hcancel, cmp89Eq251EuclideanNorm_neg_draft]
  ring

/-- The assembled central/noncentral stabilized numerator inherits the same
exact endpoint antisymmetry. -/
theorem cmp89Eq251ComplexStabilizedNumerator_swap_draft
    {d L j : ℕ} {mass alpha : ℝ} (z : Fin d → ℂ) (mu : Fin d)
    (holder transport : Fin d → ℝ) :
    cmp89Eq251ComplexStabilizedNumerator d L j mass alpha z mu
        (fun nu ↦ -holder nu) (fun nu ↦ holder nu + transport nu) =
      -cmp89Eq251ComplexStabilizedNumerator d L j mass alpha z mu
        holder transport := by
  unfold cmp89Eq251ComplexStabilizedNumerator
  simp_rw [cmp89Eq251ComplexBareAliasNumerator_swap_draft]
  ring

/-- The complete stabilized CMP89 (2.49) integrand is orientation-odd under
the source-faithful endpoint exchange. -/
theorem cmp89Eq251ComplexStabilizedIntegrand_swap_draft
    {d L j : ℕ} {mass a alpha : ℝ} (z : Fin d → ℂ) (mu : Fin d)
    (holder transport : Fin d → ℝ) :
    cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha z mu
        (fun nu ↦ -holder nu) (fun nu ↦ holder nu + transport nu) =
      -cmp89Eq251ComplexStabilizedIntegrand d L j mass a alpha z mu
        holder transport := by
  unfold cmp89Eq251ComplexStabilizedIntegrand
  rw [cmp89Eq251ComplexStabilizedNumerator_swap_draft]
  ring

/-- The other physical endpoint displacement `x-y = (x-x')+(x'-y)`. -/
def cmp89Eq249HolderFirstEndpointDisplacement_draft
    {d : ℕ} (holder transport : Fin d → ℤ) : Fin d → ℤ :=
  fun mu ↦ holder mu + transport mu

/-- Choose the transport based at `x'` when it is no longer in the signed
contour's integer `l1` length than the displacement based at `x`; otherwise
choose the exchanged endpoint.  This is not yet the CMP89 source-distance
dictionary. -/
def cmp89Eq249NearestEndpointUsesTransport_draft
    {d : ℕ} (holder transport : Fin d → ℤ) : Prop :=
  cmp89Eq251LatticeL1Length transport ≤
    cmp89Eq251LatticeL1Length
      (cmp89Eq249HolderFirstEndpointDisplacement_draft holder transport)

/-- Holder displacement after the signed-`l1` nearest-endpoint choice. -/
def cmp89Eq249NearestEndpointHolder_draft
    {d : ℕ} (holder transport : Fin d → ℤ) : Fin d → ℤ :=
  if cmp89Eq249NearestEndpointUsesTransport_draft holder transport then
    holder
  else
    fun mu ↦ -holder mu

/-- Transport displacement after the signed-`l1` nearest-endpoint choice. -/
def cmp89Eq249NearestEndpointTransport_draft
    {d : ℕ} (holder transport : Fin d → ℤ) : Fin d → ℤ :=
  if cmp89Eq249NearestEndpointUsesTransport_draft holder transport then
    transport
  else
    cmp89Eq249HolderFirstEndpointDisplacement_draft holder transport

/-- Orientation needed to recover the original ordered Holder difference
after choosing its nearer endpoint. -/
def cmp89Eq249NearestEndpointOrientation_draft
    {d : ℕ} (holder transport : Fin d → ℤ) : ℂ :=
  if cmp89Eq249NearestEndpointUsesTransport_draft holder transport then 1 else -1

/-- The selected transport length is exactly the minimum of the two literal
signed-contour `l1` endpoint lengths; no source/owner metric is silently
identified here. -/
theorem cmp89Eq251LatticeL1Length_nearestEndpointTransport_eq_min_draft
    {d : ℕ} (holder transport : Fin d → ℤ) :
    cmp89Eq251LatticeL1Length
        (cmp89Eq249NearestEndpointTransport_draft holder transport) =
      min (cmp89Eq251LatticeL1Length transport)
        (cmp89Eq251LatticeL1Length
          (cmp89Eq249HolderFirstEndpointDisplacement_draft holder transport)) := by
  by_cases hnear :
      cmp89Eq249NearestEndpointUsesTransport_draft holder transport
  · simp [cmp89Eq249NearestEndpointTransport_draft, hnear,
      cmp89Eq249NearestEndpointUsesTransport_draft, min_eq_left hnear]
  · have hfirst :
        cmp89Eq251LatticeL1Length
            (cmp89Eq249HolderFirstEndpointDisplacement_draft holder transport) ≤
          cmp89Eq251LatticeL1Length transport := le_of_not_ge hnear
    simp [cmp89Eq249NearestEndpointTransport_draft, hnear,
      min_eq_right hfirst]

/-- Choosing the nearer endpoint preserves the literal unit Holder edge. -/
theorem cmp89Eq249NearestEndpointHolder_unit_draft
    {d : ℕ} {holder transport : Fin d → ℤ}
    (hunit : CMP89Eq251UnitLatticeBondDisplacement holder) :
    CMP89Eq251UnitLatticeBondDisplacement
      (cmp89Eq249NearestEndpointHolder_draft holder transport) := by
  by_cases hnear :
      cmp89Eq249NearestEndpointUsesTransport_draft holder transport
  · simpa [cmp89Eq249NearestEndpointHolder_draft, hnear] using hunit
  · unfold CMP89Eq251UnitLatticeBondDisplacement at hunit ⊢
    simp [cmp89Eq249NearestEndpointHolder_draft, hnear,
      cmp89Eq251LatticeL1Length]
    exact hunit

/-- The orientation and nearest-endpoint data recover the original complete
integrand exactly.  The endpoint is selected internally rather than supplied
as a caller-chosen branch. -/
theorem
    cmp89Eq251ComplexStabilizedIntegrand_physicalFine_eq_orientation_mul_nearest_draft
    {L j : ℕ} {mass a alpha : ℝ} (z : Fin 4 → ℂ) (mu : Fin 4)
    (holder transport : Fin 4 → ℤ) :
    let xi := cmp89Eq249FineLatticeSpacing L j
    cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha z mu
        (cmp89Eq249PhysicalFineLatticeDisplacement xi holder)
        (cmp89Eq249PhysicalFineLatticeDisplacement xi transport) =
      cmp89Eq249NearestEndpointOrientation_draft holder transport *
        cmp89Eq251ComplexStabilizedIntegrand 4 L j mass a alpha z mu
          (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (cmp89Eq249NearestEndpointHolder_draft holder transport))
          (cmp89Eq249PhysicalFineLatticeDisplacement xi
            (cmp89Eq249NearestEndpointTransport_draft holder transport)) := by
  dsimp only
  let xi := cmp89Eq249FineLatticeSpacing L j
  by_cases hnear :
      cmp89Eq249NearestEndpointUsesTransport_draft holder transport
  · simp [cmp89Eq249NearestEndpointOrientation_draft,
      cmp89Eq249NearestEndpointHolder_draft,
      cmp89Eq249NearestEndpointTransport_draft, hnear]
  · have hholder :
        cmp89Eq249PhysicalFineLatticeDisplacement xi
            (fun nu ↦ -holder nu) =
          fun nu ↦ -cmp89Eq249PhysicalFineLatticeDisplacement xi holder nu := by
      funext nu
      simp [cmp89Eq249PhysicalFineLatticeDisplacement]
      ring
    have hfirst :
        cmp89Eq249PhysicalFineLatticeDisplacement xi
            (cmp89Eq249HolderFirstEndpointDisplacement_draft holder transport) =
          fun nu ↦ cmp89Eq249PhysicalFineLatticeDisplacement xi holder nu +
            cmp89Eq249PhysicalFineLatticeDisplacement xi transport nu := by
      funext nu
      simp [cmp89Eq249HolderFirstEndpointDisplacement_draft,
        cmp89Eq249PhysicalFineLatticeDisplacement]
      ring
    simp only [cmp89Eq249NearestEndpointOrientation_draft,
      cmp89Eq249NearestEndpointHolder_draft,
      cmp89Eq249NearestEndpointTransport_draft, hnear, if_false]
    rw [hholder, hfirst,
      cmp89Eq251ComplexStabilizedIntegrand_swap_draft
        (z := z) (mu := mu)
        (cmp89Eq249PhysicalFineLatticeDisplacement xi holder)
        (cmp89Eq249PhysicalFineLatticeDisplacement xi transport)]
    ring

end

end YangMills.RG
