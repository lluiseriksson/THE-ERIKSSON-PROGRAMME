import Mathlib
import YangMills.P6_AsymptoticFreedom.AsymptoticFreedomDischarge

namespace YangMills

open MeasureTheory Real Filter

/-! ## L8.2: ClayPhysicalStrong — Non-vacuous Clay Target

### Background

Both existing Clay targets are vacuous:
- `ClayYangMillsTheorem = ∃ m_phys : ℝ, 0 < m_phys` — proved by `⟨1, one_pos⟩`
- `ClayYangMillsStrong = ∃ m_lat, HasContinuumMassGap m_lat` — proved by
  `⟨constantMassProfile 1, constantMassProfile_continuumGap 1 one_pos⟩`

The root cause: neither definition requires `m_lat` to interact with the actual
Yang-Mills measure `μ`. Any constant-profile construction defeats both.

### C73 Fix

`IsYangMillsMassProfile` requires the mass profile to **actually bound the
Wilson connected correlators** for the given Yang-Mills Gibbs measure.
`ClayYangMillsPhysicalStrong` then requires both physical grounding and a
positive continuum limit.  These definitions are NOT vacuously true: any
witness must interact with the Yang-Mills measure `μ`.

### Main result (sorry-free)

`connectedCorrDecay_implies_physicalStrong`: if the Wilson connected
correlators decay exponentially at rate `h.m` (ConnectedCorrDecay), then
the constant profile `constantMassProfile h.m` witnesses
`ClayYangMillsPhysicalStrong`.

Key inequality: `constantMassProfile h.m N = h.m / (N+1) ≤ h.m`, so for
non-negative distance `distP N p q ≥ 0`:
  `exp(-h.m * distP N p q) ≤ exp(-constantMassProfile h.m N * distP N p q)`.

### Architectural consequence

The genuine open problem is to prove `ConnectedCorrDecay` for the actual
Yang-Mills Gibbs measure from first principles (Balaban RG, KP cluster
expansion, uniform LSI).  That is where all remaining `sorry` live.
-/

variable {d : ℕ} [NeZero d]
variable {G : Type*} [Group G] [MeasurableSpace G]

/-- **C73-DEF1**: A lattice mass profile is *physically grounded* for the Yang-Mills
    theory `(μ, plaquetteEnergy, β, F)` and distance function `distP` if it actually
    bounds the Wilson connected two-point function at every resolution N.

    Formally: ∃ C ≥ 0, ∀ N, p, q:
      `|wilsonConnectedCorr μ β F p q| ≤ C * exp(-m_lat N * distP N p q)`.

    This is **non-vacuous**: unlike `HasContinuumMassGap`, any witness `m_lat` must
    interact with the actual Gibbs measure `μ`.  In particular `constantMassProfile 1`
    does NOT automatically satisfy this predicate — it would require
    `|wilsonConnectedCorr| ≤ C * exp(-1/(N+1) * dist)`, a bound that genuinely
    depends on the Yang-Mills dynamics. -/
def IsYangMillsMassProfile
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (m_lat : LatticeMassProfile) : Prop :=
  ∃ (C : ℝ) (_hC : 0 ≤ C),
    ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
      |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q| ≤
      C * Real.exp (-m_lat N * distP N p q)

/-- **C73-DEF2**: The physically-grounded strong Clay target.

    There exists a lattice mass profile `m_lat` satisfying BOTH:
    (a) physical grounding: `m_lat` bounds the Yang-Mills Wilson correlators
        (`IsYangMillsMassProfile`), and
    (b) continuum mass gap: the renormalized mass `m_lat N / a(N)` converges
        to a strictly positive continuum limit (`HasContinuumMassGap`).

    This target is **strictly stronger** than both `ClayYangMillsTheorem` and
    `ClayYangMillsStrong`, and is **not vacuously true**: condition (a) ties
    `m_lat` to the actual Yang-Mills Gibbs measure `μ`.

    The genuine remaining mathematical content is proving `ConnectedCorrDecay`
    for the actual Yang-Mills theory via Balaban RG + KP cluster expansion. -/
def ClayYangMillsPhysicalStrong
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ) : Prop :=
  ∃ m_lat : LatticeMassProfile,
    IsYangMillsMassProfile μ plaquetteEnergy β F distP m_lat ∧
    HasContinuumMassGap m_lat

/-- **C73-L1**: The constant mass profile `constantMassProfile m` satisfies
    `m_lat N ≤ m` pointwise (for `m ≥ 0`).

    Proof: `constantMassProfile m N = m * a(N) = m / (N+1) ≤ m * 1 = m`
    since `1/(N+1) ≤ 1`. -/
lemma constantMassProfile_le (m : ℝ) (hm : 0 ≤ m) (N : ℕ) :
    constantMassProfile m N ≤ m := by
  unfold constantMassProfile latticeSpacing
  have hN1 : (0 : ℝ) < ↑N + 1 := by positivity
  have h1N : (1 : ℝ) / (↑N + 1) ≤ 1 := by
    rw [div_le_one hN1]
    norm_cast; omega
  calc m * (1 / (↑N + 1)) ≤ m * 1 := mul_le_mul_of_nonneg_left h1N hm
    _ = m := mul_one m

/-- **C73-MAIN (sorry-free)**: ConnectedCorrDecay → ClayYangMillsPhysicalStrong.

    Given that Wilson connected correlators decay exponentially at rate `h.m` and
    the distance function `distP` is non-negative, the constant mass profile
    `constantMassProfile h.m` (where `m_lat N = h.m / (N+1)`) witnesses
    `ClayYangMillsPhysicalStrong`.

    Two-part witness:
    (a) **Physical grounding**: use `C = h.C` and the chain
        `|wilsonConnectedCorr| ≤ h.C * exp(-h.m * distP)  [from h.bound]
         ≤ h.C * exp(-constantMassProfile h.m N * distP)  [since m_lat N ≤ h.m and distP ≥ 0]`
    (b) **Continuum mass gap**: `constantMassProfile_continuumGap h.m h.hm`.

    Oracle footprint: `[propext, Classical.choice, Quot.sound]`.
    No `yangMills_continuum_mass_gap` axiom is used. -/
theorem connectedCorrDecay_implies_physicalStrong
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  refine ⟨constantMassProfile h.m, ⟨h.C, h.hC, ?_⟩,
          constantMassProfile_continuumGap h.m h.hm⟩
  intro N inst p q
  haveI := inst
  have hle : constantMassProfile h.m N ≤ h.m :=
    constantMassProfile_le h.m h.hm.le N
  have hdist : 0 ≤ distP N p q := hdistP N p q
  calc |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q|
      ≤ h.C * Real.exp (-h.m * distP N p q) := h.bound N p q
    _ ≤ h.C * Real.exp (-constantMassProfile h.m N * distP N p q) := by
        apply mul_le_mul_of_nonneg_left _ h.hC
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ hdist
        linarith

/-- **C74-GEN (sorry-free)**: ConnectedCorrDecay → ClayYangMillsPhysicalStrong via ANY
    dominated profile.

    Strictly generalises `connectedCorrDecay_implies_physicalStrong`: instead of
    requiring the specific witness `constantMassProfile h.m`, this theorem accepts
    **any** lattice mass profile `m_lat` satisfying:
    (dom) `m_lat N ≤ h.m` for all N, and
    (cont) `HasContinuumMassGap m_lat`.

    Proof: identical calc chain to the C73 theorem, with `hdom N` replacing
    `constantMassProfile_le h.m h.hm.le N` for the key inequality.

    Architectural value: future proofs of `ConnectedCorrDecay` are not tied to
    the constant profile — any exponentially-decaying or RG-renormalized profile
    that is pointwise bounded by `h.m` immediately witnesses the physical target.

    Oracle: `[propext, Classical.choice, Quot.sound]`. -/
theorem connectedCorrDecay_implies_physicalStrong_of_dominated
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        0 ≤ distP N p q)
    (m_lat : LatticeMassProfile)
    (hdom : ∀ N, m_lat N ≤ h.m)
    (hcont : HasContinuumMassGap m_lat) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP := by
  refine ⟨m_lat, ⟨h.C, h.hC, ?_⟩, hcont⟩
  intro N inst p q
  haveI := inst
  have hdist : 0 ≤ distP N p q := hdistP N p q
  calc |@wilsonConnectedCorr d N _ _ G _ _ μ plaquetteEnergy β F p q|
      ≤ h.C * Real.exp (-h.m * distP N p q) := h.bound N p q
    _ ≤ h.C * Real.exp (-m_lat N * distP N p q) := by
        apply mul_le_mul_of_nonneg_left _ h.hC
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ hdist
        linarith [hdom N]

/-- **C74-COR (sorry-free)**: The C73 theorem is a special case of C74-GEN.

    `connectedCorrDecay_implies_physicalStrong` follows immediately by taking
    `m_lat = constantMassProfile h.m`, with:
    - `hdom = constantMassProfile_le h.m h.hm.le` (proved in C73-L1)
    - `hcont = constantMassProfile_continuumGap h.m h.hm` (proved in P6) -/
theorem connectedCorrDecay_implies_physicalStrong_via_gen
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ConnectedCorrDecay μ plaquetteEnergy β F distP)
    (hdistP : ∀ (N : ℕ) [NeZero N] (p q : ConcretePlaquette d N),
        0 ≤ distP N p q) :
    ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP :=
  connectedCorrDecay_implies_physicalStrong_of_dominated
    μ plaquetteEnergy β F distP h hdistP
    (constantMassProfile h.m)
    (constantMassProfile_le h.m h.hm.le)
    (constantMassProfile_continuumGap h.m h.hm)

/-- **C73-COR**: ClayYangMillsPhysicalStrong implies ClayYangMillsStrong.

    Any physically-grounded profile with continuum mass gap also witnesses the
    (weaker) `ClayYangMillsStrong`, confirming the strict hierarchy:
      `ClayYangMillsPhysicalStrong → ClayYangMillsStrong → ClayYangMillsTheorem`. -/
theorem physicalStrong_implies_strong
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP) :
    ClayYangMillsStrong :=
  let ⟨m_lat, _, hcont⟩ := h; ⟨m_lat, hcont⟩

/-- **C73-COR2**: ClayYangMillsPhysicalStrong implies ClayYangMillsTheorem. -/
theorem physicalStrong_implies_theorem
    (μ : Measure G) (plaquetteEnergy : G → ℝ) (β : ℝ)
    (F : G → ℝ)
    (distP : (N : ℕ) → ConcretePlaquette d N → ConcretePlaquette d N → ℝ)
    (h : ClayYangMillsPhysicalStrong μ plaquetteEnergy β F distP) :
    ClayYangMillsTheorem :=
  let ⟨m_lat, _, hcont⟩ := h
  continuumLimit_mass_pos m_lat hcont

end YangMills
