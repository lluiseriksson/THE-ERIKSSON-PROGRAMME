/- Copyright (c) 2026 Lluis Eriksson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lluis Eriksson -/
import YangMills.ClayCore.LatticeAnimalCount
import YangMills.ClayCore.ClusterRpowBridge

/-!
# Lattice-animal F3 bridge

Small terminal bridge from the concrete physical lattice-animal count target to
the physical-only exponential F3 package.

No sorry. No new axioms.
-/

namespace YangMills

/-- Package the live physical `1296` decoder target together with the physical
Mayer half and the KP smallness condition as the physical-only exponential F3
frontier object. -/
def physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    PhysicalOnlyShiftedF3MayerCountPackageExp N_c wab :=
  PhysicalOnlyShiftedF3MayerCountPackageExp.ofSubpackages mayer
    (physicalShiftedF3CountPackageExp_of_baselineExtraWordDecoderCovers1296 hcover)
    hKr_lt1

@[simp] theorem physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296_C_conn
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    (physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296
      wab mayer hcover hKr_lt1).count.C_conn = 1 := rfl

@[simp] theorem physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296_K
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    (physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296
      wab mayer hcover hKr_lt1).count.K = 1296 := rfl

@[simp] theorem physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296_A₀
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    (physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296
      wab mayer hcover hKr_lt1).mayer.A₀ = mayer.A₀ := rfl

/-- Terminal physical exponential F3 bridge from the live `1296` decoder target
and the physical Mayer half to the Wilson-facing physical cluster-correlator
bound. -/
theorem physicalClusterCorrelatorBound_of_baselineExtraWordDecoderCovers1296
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hcover : PhysicalConnectingClusterBaselineExtraWordDecoderCovers1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    let pkg :=
      physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296
        wab mayer hcover hKr_lt1
    PhysicalClusterCorrelatorBound N_c wab.r
      (clusterPrefactorExp wab.r pkg.count.K pkg.count.C_conn pkg.mayer.A₀) :=
  physicalClusterCorrelatorBound_of_physicalOnlyShiftedF3MayerCountPackageExp
    wab
    (physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296
      wab mayer hcover hKr_lt1)

/-- Package the shifted graph-animal `1296` count target together with the
physical Mayer half and the KP smallness condition as the physical-only
exponential F3 frontier object. -/
def physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hgraph : PhysicalConnectingClusterGraphAnimalShiftedCountBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    PhysicalOnlyShiftedF3MayerCountPackageExp N_c wab :=
  PhysicalOnlyShiftedF3MayerCountPackageExp.ofSubpackages mayer
    (physicalShiftedF3CountPackageExp_of_graphAnimalShiftedCount1296 hgraph)
    hKr_lt1

@[simp] theorem physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296_C_conn
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hgraph : PhysicalConnectingClusterGraphAnimalShiftedCountBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    (physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296
      wab mayer hgraph hKr_lt1).count.C_conn = 1 := rfl

@[simp] theorem physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296_K
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hgraph : PhysicalConnectingClusterGraphAnimalShiftedCountBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    (physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296
      wab mayer hgraph hKr_lt1).count.K = 1296 := rfl

@[simp] theorem physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296_A₀
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hgraph : PhysicalConnectingClusterGraphAnimalShiftedCountBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    (physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296
      wab mayer hgraph hKr_lt1).mayer.A₀ = mayer.A₀ := rfl

/-- Terminal physical exponential F3 bridge from the shifted graph-animal
`1296` count target and the physical Mayer half to the Wilson-facing physical
cluster-correlator bound. -/
theorem physicalClusterCorrelatorBound_of_graphAnimalShiftedCount1296
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hgraph : PhysicalConnectingClusterGraphAnimalShiftedCountBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    let pkg :=
      physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296
        wab mayer hgraph hKr_lt1
    PhysicalClusterCorrelatorBound N_c wab.r
      (clusterPrefactorExp wab.r pkg.count.K pkg.count.C_conn pkg.mayer.A₀) :=
  physicalClusterCorrelatorBound_of_physicalOnlyShiftedF3MayerCountPackageExp
    wab
    (physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296
      wab mayer hgraph hKr_lt1)

/-- Package the shifted graph-animal `1296` word-decoder target together with
the physical Mayer half and the KP smallness condition as the physical-only
exponential F3 frontier object. -/
def physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hdecode : PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    PhysicalOnlyShiftedF3MayerCountPackageExp N_c wab :=
  PhysicalOnlyShiftedF3MayerCountPackageExp.ofSubpackages mayer
    (physicalShiftedF3CountPackageExp_of_graphAnimalWordDecoder1296 hdecode)
    hKr_lt1

@[simp] theorem physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296_C_conn
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hdecode : PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    (physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296
      wab mayer hdecode hKr_lt1).count.C_conn = 1 := rfl

@[simp] theorem physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296_K
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hdecode : PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    (physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296
      wab mayer hdecode hKr_lt1).count.K = 1296 := rfl

@[simp] theorem physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296_A₀
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hdecode : PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    (physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296
      wab mayer hdecode hKr_lt1).mayer.A₀ = mayer.A₀ := rfl

/-- Terminal physical exponential F3 bridge from the shifted graph-animal
`1296` word-decoder target and the physical Mayer half to the Wilson-facing
physical cluster-correlator bound. -/
theorem physicalClusterCorrelatorBound_of_graphAnimalWordDecoder1296
    {N_c : ℕ} [NeZero N_c]
    (wab : WilsonPolymerActivityBound N_c)
    (mayer : PhysicalShiftedF3MayerPackage N_c wab)
    (hdecode : PhysicalConnectingClusterGraphAnimalShiftedWordDecoderBound1296)
    (hKr_lt1 : (1296 : ℝ) * wab.r < 1) :
    let pkg :=
      physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296
        wab mayer hdecode hKr_lt1
    PhysicalClusterCorrelatorBound N_c wab.r
      (clusterPrefactorExp wab.r pkg.count.K pkg.count.C_conn pkg.mayer.A₀) :=
  physicalClusterCorrelatorBound_of_physicalOnlyShiftedF3MayerCountPackageExp
    wab
    (physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296
      wab mayer hdecode hKr_lt1)

#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296_C_conn
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296_K
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_baselineExtraWordDecoderCovers1296_A₀
#print axioms physicalClusterCorrelatorBound_of_baselineExtraWordDecoderCovers1296
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296_C_conn
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296_K
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalShiftedCount1296_A₀
#print axioms physicalClusterCorrelatorBound_of_graphAnimalShiftedCount1296
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296_C_conn
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296_K
#print axioms physicalOnlyShiftedF3MayerCountPackageExp_of_graphAnimalWordDecoder1296_A₀
#print axioms physicalClusterCorrelatorBound_of_graphAnimalWordDecoder1296

end YangMills
