/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceRegionalCoarseAverage

/-!
# Canonical multiscale realizations of a CMP99 source region

Printed CMP99 p. 408 uses two independent indices.  The index `r` selects a
domain `Omega_r(Pi)` in the local nested sequence, whereas the averaging order
changes the lattice on which that same domain is realized.  This file keeps
those roles separate.

Starting from the literal large-block carrier of one `Omega_r(Pi)`, it lifts
the carrier recursively through complete order-`M` blocks.  Every positive
level is block-saturated and complete-block coarsening returns the preceding
level as an equality of `ActiveGaugeRegion` objects.  Thus the dependent field
types used by consecutive regional averages match without an unaudited cast.

No formula for the global nested domains is invented here.  In CMP99 they are
inherited from the geometric setting of CMP96 (conditions (2.1)--(2.4)); the
local construction on printed p. 408 only specifies their realization around
one partition cube.
-/

namespace YangMills.RG

noncomputable section

/-- Lattice side after `k` successive order-`M` fine realizations. -/
def cmp99RegionalLatticeSize (M N : ℕ) : ℕ → ℕ
  | 0 => N
  | k + 1 => M * cmp99RegionalLatticeSize M N k

@[simp] theorem cmp99RegionalLatticeSize_zero (M N : ℕ) :
    cmp99RegionalLatticeSize M N 0 = N := rfl

@[simp] theorem cmp99RegionalLatticeSize_succ (M N k : ℕ) :
    cmp99RegionalLatticeSize M N (k + 1) =
      M * cmp99RegionalLatticeSize M N k := rfl

instance cmp99RegionalLatticeSize_neZero
    (M N k : ℕ) [NeZero M] [NeZero N] :
    NeZero (cmp99RegionalLatticeSize M N k) := by
  induction k with
  | zero => simpa using (inferInstance : NeZero N)
  | succ k ih =>
      simp only [cmp99RegionalLatticeSize_succ]
      letI : NeZero (cmp99RegionalLatticeSize M N k) := ih
      infer_instance

/-- Realize one coarse active region on the lattice `k` orders finer. -/
noncomputable def cmp99IteratedLiftActiveRegion
    {d M N : ℕ} [NeZero M] [NeZero N]
    (Omega : ActiveGaugeRegion d N) :
    (k : ℕ) → ActiveGaugeRegion d (cmp99RegionalLatticeSize M N k)
  | 0 => Omega
  | k + 1 => cmp99LiftActiveRegion (M := M)
      (cmp99IteratedLiftActiveRegion Omega k)

@[simp] theorem cmp99IteratedLiftActiveRegion_zero
    {d M N : ℕ} [NeZero M] [NeZero N]
    (Omega : ActiveGaugeRegion d N) :
    cmp99IteratedLiftActiveRegion (M := M) Omega 0 = Omega := rfl

@[simp] theorem cmp99IteratedLiftActiveRegion_succ
    {d M N : ℕ} [NeZero M] [NeZero N]
    (Omega : ActiveGaugeRegion d N) (k : ℕ) :
    cmp99IteratedLiftActiveRegion (M := M) Omega (k + 1) =
      cmp99LiftActiveRegion (M := M)
        (cmp99IteratedLiftActiveRegion (M := M) Omega k) := rfl

/-- Every nonzero multiscale realization is made of complete blocks. -/
theorem cmp99IteratedLiftActiveRegion_blockSaturated
    {d M N : ℕ} [NeZero M] [NeZero N]
    (Omega : ActiveGaugeRegion d N) (k : ℕ) :
    (cmp99IteratedLiftActiveRegion (M := M) Omega (k + 1)).BlockSaturated := by
  rw [cmp99IteratedLiftActiveRegion_succ]
  exact cmp99LiftActiveRegion_blockSaturated
    (cmp99IteratedLiftActiveRegion (M := M) Omega k)

/-- The typed transition required by the physical regional tower: coarsening
level `k+1` is literally level `k`. -/
theorem cmp99ActiveCoarseRegion_iteratedLift_succ_eq
    {d M N : ℕ} [NeZero M] [NeZero N]
    (Omega : ActiveGaugeRegion d N) (k : ℕ) :
    cmp99ActiveCoarseRegion (M := M)
        (N' := cmp99RegionalLatticeSize M N k)
        (cmp99IteratedLiftActiveRegion (M := M) Omega (k + 1)) =
      cmp99IteratedLiftActiveRegion (M := M) Omega k := by
  rw [cmp99IteratedLiftActiveRegion_succ]
  exact cmp99ActiveCoarseRegion_lift_eq
    (cmp99IteratedLiftActiveRegion (M := M) Omega k)

variable {Q j : ℕ} [NeZero Q]
variable {cell : FinBox 4 Q}

/-- Coarsest active-region object carried by one literal source domain
`Omega_r(Pi)`. -/
def cmp99OmegaCoarseActiveGaugeRegion
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    ActiveGaugeRegion 4 (2 * Q) where
  sites := Seq.regions r

@[simp] theorem cmp99OmegaCoarseActiveGaugeRegion_sites
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) :
    (cmp99OmegaCoarseActiveGaugeRegion Seq r).sites = Seq.regions r := rfl

/-- The canonical scale-`k` realization of the selected source domain. -/
noncomputable def cmp99OmegaScaleActiveGaugeRegion
    {M : ℕ} [NeZero M]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) (k : ℕ) :
    ActiveGaugeRegion 4 (cmp99RegionalLatticeSize M (2 * Q) k) :=
  cmp99IteratedLiftActiveRegion (M := M)
    (cmp99OmegaCoarseActiveGaugeRegion Seq r) k

/-- Every positive-resolution source region is block-saturated. -/
theorem cmp99OmegaScaleActiveGaugeRegion_blockSaturated
    {M : ℕ} [NeZero M]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) (k : ℕ) :
    (cmp99OmegaScaleActiveGaugeRegion (M := M) Seq r (k + 1)).BlockSaturated :=
  cmp99IteratedLiftActiveRegion_blockSaturated
    (cmp99OmegaCoarseActiveGaugeRegion Seq r) k

/-- Exact dependent equality between consecutive scale realizations of one
literal `Omega_r(Pi)`. -/
theorem cmp99ActiveCoarseRegion_omegaScale_succ_eq
    {M : ℕ} [NeZero M]
    (Seq : CMP99SourceOmegaGeometry cell j) (r : Fin (j + 2)) (k : ℕ) :
    cmp99ActiveCoarseRegion (M := M)
        (N' := cmp99RegionalLatticeSize M (2 * Q) k)
        (cmp99OmegaScaleActiveGaugeRegion (M := M) Seq r (k + 1)) =
      cmp99OmegaScaleActiveGaugeRegion (M := M) Seq r k :=
  cmp99ActiveCoarseRegion_iteratedLift_succ_eq
    (cmp99OmegaCoarseActiveGaugeRegion Seq r) k

end

end YangMills.RG
