/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under the GNU Affero General Public License v3.0
as described in the file LICENSE.
Authors: Lluis Eriksson -/

import YangMills.RG.BalabanCMP99SourceFlatGeneratedQprimeComplexification

/-!
# Fourier action of the generated flat CMP99 `Q'` recursion

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and the result has not yet been verified by the Lean compiler.

The generated flat physical tower is a typed recursion through the literal
active coarse regions.  This file first proves that its explicit complex
one-step maps, and hence the complete forward and reverse recursions, are
complex homogeneous despite being bundled as real continuous-linear maps.
It then constructs the scalar Fourier amplitude and terminal restricted mode
recursively along that same typed chain and proves their exact forward action.

Honest scope: the endpoint retains every prefix alias and every active region.
It does not identify distinct CMP99 source strata, replace the recursion by a
single terminal block average, construct a global Fourier equivalence, match
the generated real precision with a separately reconstructed complex
precision, construct an inverse, or produce a regional Green bound.
-/

namespace YangMills.RG

open YangMills

noncomputable section

variable {d M N Nc : ℕ}
variable [NeZero d] [NeZero M] [NeZero N] [NeZero Nc]

omit [NeZero d] [NeZero Nc] in
/-- The explicit one-step flat complex average is complex homogeneous. -/
theorem cmp99SourceFlatComplexBlockAverageCLM_map_complex_smul
    {N' : ℕ} [NeZero N'] (Omega : ActiveGaugeRegion d (M * N'))
    (c : ℂ)
    (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc)) :
    cmp99SourceFlatComplexBlockAverageCLM Omega (c • phi) =
      c • cmp99SourceFlatComplexBlockAverageCLM Omega phi := by
  apply WithLp.ofLp_injective
  funext y
  change cmp99SourceFlatComplexBlockAverageCLM Omega (c • phi) y =
    c • cmp99SourceFlatComplexBlockAverageCLM Omega phi y
  rw [cmp99SourceFlatComplexBlockAverageCLM_apply,
    cmp99SourceFlatComplexBlockAverageCLM_apply]
  simp only [PiLp.smul_apply]
  rw [← Finset.smul_sum]
  exact smul_comm (M := ℝ) (N := ℂ)
    (α := SUNLieComplexCoord Nc) _ _ _

omit [NeZero d] [NeZero Nc] in
/-- The explicit one-step coefficient-one synthesis is complex homogeneous. -/
theorem cmp99SourceFlatComplexBlockWeightedAdjointCLM_map_complex_smul
    {N' : ℕ} [NeZero N'] (Omega : ActiveGaugeRegion d (M * N'))
    (hOmega : Omega.BlockSaturated) (c : ℂ)
    (eta : ActiveGaugeZeroCochain
      (cmp99ActiveCoarseRegion (M := M) (N' := N') Omega)
      (SUNLieComplexCoord Nc)) :
    cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega (c • eta) =
      c • cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega eta := by
  apply WithLp.ofLp_injective
  funext x
  change cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega
      (c • eta) x =
    c • cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega eta x
  rw [cmp99SourceFlatComplexBlockWeightedAdjointCLM_apply,
    cmp99SourceFlatComplexBlockWeightedAdjointCLM_apply]
  rfl

/-- The complete generated forward complex recursion is complex homogeneous.
This is proved from the literal one-step maps rather than supplied as a
property of an external complex operator family. -/
omit [NeZero d] [NeZero Nc] in
theorem CMP99SourceActiveRegionChain.flatExplicitComplexQprime_map_complex_smul
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ (c : ℂ) (phi : ActiveGaugeZeroCochain Omega (SUNLieComplexCoord Nc)),
      regions.flatExplicitComplexQprime (c • phi) =
        c • regions.flatExplicitComplexQprime phi := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro c phi
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro c phi
      change tail.flatExplicitComplexQprime
          (cmp99SourceFlatComplexBlockAverageCLM Omega (c • phi)) =
        c • tail.flatExplicitComplexQprime
          (cmp99SourceFlatComplexBlockAverageCLM Omega phi)
      rw [cmp99SourceFlatComplexBlockAverageCLM_map_complex_smul, ih]

/-- The complete generated reverse coefficient-one synthesis is complex
homogeneous as well. -/
omit [NeZero d] [NeZero Nc] in
theorem
    CMP99SourceActiveRegionChain.flatExplicitComplexWeightedAdjoint_map_complex_smul
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ (c : ℂ)
      (eta : PiLp 2 (fun _ : regions.terminalSite => SUNLieComplexCoord Nc)),
      regions.flatExplicitComplexWeightedAdjoint (c • eta) =
        c • regions.flatExplicitComplexWeightedAdjoint eta := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro c eta
      rfl
  | @step N' depth _ Omega hOmega tail ih =>
      intro c eta
      change cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega
          (tail.flatExplicitComplexWeightedAdjoint (c • eta)) =
        c • cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega
          (tail.flatExplicitComplexWeightedAdjoint eta)
      calc
        _ = cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega
              (c • tail.flatExplicitComplexWeightedAdjoint eta) :=
            congrArg
              (fun z =>
                cmp99SourceFlatComplexBlockWeightedAdjointCLM Omega hOmega z)
              (ih c eta)
        _ = _ :=
          cmp99SourceFlatComplexBlockWeightedAdjointCLM_map_complex_smul
            Omega hOmega c _

/-- Product of the literal one-step Fourier amplitudes along one typed active
region chain.  Every reciprocal alias is generated internally at its prefix. -/
noncomputable def CMP99SourceActiveRegionChain.flatFourierAmplitude
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    FinBox d N → ℂ := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      exact fun _ => 1
  | @step N' depth _ Omega hOmega tail ih =>
      exact fun k =>
        cmp89Eq245EntireAverageAmplitude d M
            (cmp99SourceFlatQprimeAmplitudeMomentum k) *
          ih (cmp99SourceFlatQprimeCoarseAlias k)

/-- The terminal restricted Fourier mode obtained by following the literal
coarse reciprocal alias at every prefix of the typed active-region chain. -/
noncomputable def CMP99SourceActiveRegionChain.flatFourierTerminalMode
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    FinBox d N → SUNLieComplexCoord Nc →
      PiLp 2 (fun _ : regions.terminalSite => SUNLieComplexCoord Nc) := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      exact fun k v => cmp99SourceFlatActiveComplexFibreFourierMode Omega k v
  | @step N' depth _ Omega hOmega tail ih =>
      exact fun k v => ih (cmp99SourceFlatQprimeCoarseAlias k) v

/-- Exact Fourier action of the complete generated flat complex `Q'`
recursion.  The conclusion is recursive by construction: it keeps the
product of prefix amplitudes and the terminal mode reached by the matching
sequence of reciprocal aliases. -/
theorem CMP99SourceActiveRegionChain.flatExplicitComplexQprime_fourierMode
    {N depth : ℕ} {Omega : ActiveGaugeRegion d N}
    (regions : CMP99SourceActiveRegionChain d M N Omega depth) :
    letI : NeZero N := regions.neZero
    ∀ (k : FinBox d N) (v : SUNLieComplexCoord Nc),
      regions.flatExplicitComplexQprime
          (cmp99SourceFlatActiveComplexFibreFourierMode Omega k v) =
        regions.flatFourierAmplitude k •
          regions.flatFourierTerminalMode k v := by
  letI : NeZero N := regions.neZero
  induction regions with
  | stop Omega =>
      intro k v
      change cmp99SourceFlatActiveComplexFibreFourierMode Omega k v =
        (1 : ℂ) • cmp99SourceFlatActiveComplexFibreFourierMode Omega k v
      simp
  | @step N' depth _ Omega hOmega tail ih =>
      intro k v
      change tail.flatExplicitComplexQprime
          (cmp99SourceFlatComplexBlockAverageCLM Omega
            (cmp99SourceFlatActiveComplexFibreFourierMode Omega k v)) =
        (cmp89Eq245EntireAverageAmplitude d M
              (cmp99SourceFlatQprimeAmplitudeMomentum k) *
            tail.flatFourierAmplitude
              (cmp99SourceFlatQprimeCoarseAlias k)) •
          tail.flatFourierTerminalMode
            (cmp99SourceFlatQprimeCoarseAlias k) v
      rw [cmp99SourceFlatComplexBlockAverage_fourierMode,
        tail.flatExplicitComplexQprime_map_complex_smul, ih, smul_smul]

end

end YangMills.RG
