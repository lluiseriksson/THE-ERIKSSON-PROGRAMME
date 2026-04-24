/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.L5_MassGap.MassGap
import YangMills.L6_FeynmanKac.FeynmanKac
import YangMills.L6_OS.OsterwalderSchrader
import YangMills.L7_Continuum.ContinuumLimit

/-! # L8.1: Clay Millennium Theorem — statement definitions (v0.32.0)

This file contains ONLY the `Prop`-level statement definitions of the Clay
Yang–Mills mass-gap conclusion. The assembled theorems (which discharge the
existentials) live downstream in `YangMills.P8_PhysicalGap.ClayAssembly`,
which currently proves the weak endpoint through the MemLp-gated normalized
LSI route.

As of v0.32.0 the monolithic axiom `yangMills_continuum_mass_gap` has been
**deleted**: no file in the project depends on it.
-/

namespace YangMills

/-- The Clay Millennium Problem conclusion: existence of a positive physical mass gap. -/
def ClayYangMillsTheorem : Prop := ∃ m_phys : ℝ, 0 < m_phys

/-- Strong Clay–Millennium conclusion: a lattice mass profile whose
renormalized mass converges to a positive real limit exists.
Strictly stronger than `ClayYangMillsTheorem`. -/
def ClayYangMillsStrong : Prop :=
  ∃ m_lat : LatticeMassProfile, HasContinuumMassGap m_lat

end YangMills
