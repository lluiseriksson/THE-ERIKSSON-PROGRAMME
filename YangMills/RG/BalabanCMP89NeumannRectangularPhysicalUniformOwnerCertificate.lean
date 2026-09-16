import YangMills.RG.BalabanCMP89NeumannRectangularPhysicalUniformOwnerBound

/-!
# CMP89 rectangular regional Green: uniform owner-kernel certificate

This packages the cold-sealed physical owner estimate into one explicit,
depth-independent amplitude and owner rate.  It remains a scalar pointwise
kernel certificate.  In particular it is not the arbitrary-field localized
action estimate of CMP99 (3.42), whose `[ell^2, ell, ell, 1]` scale vector
cannot be obtained by summing this estimate over a fine owner fibre.
-/

namespace YangMills.RG

noncomputable section

/-- A scalar or vector-valued kernel with exponential decay in a named owner
metric.  The kernel, owner map, metric and both constants are parameters of
the proposition rather than hidden choices. -/
structure CMP89RegionalOwnerKernelDecayCertificate
    {ι β E : Type*} [Norm E]
    (kernel : ι → ι → E) (owner : ι → β) (dist : β → β → ℕ)
    (B0 delta0 : ℝ) : Prop where
  B0_nonneg : 0 ≤ B0
  delta0_pos : 0 < delta0
  bound : ∀ x y,
    ‖kernel x y‖ ≤
      B0 * Real.exp (-(delta0 * (dist (owner x) (owner y) : ℝ)))

/-- Explicit depth-free amplitude produced by the CMP89 reflection sum,
period floor and physical owner geometry.  Every geometric payment remains
visible: `2^4` reflection branches, the coordinatewise period product and
the exact `exp (2*rho)` rectangle-boundary loss. -/
def cmp89Eq248PhysicalRegionalUniformOwnerB0_draft
    (a rho : ℝ) : ℝ :=
  (2 : ℝ) ^ 4 *
    cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho *
    ((2 / (1 - Real.exp (-rho))) ^ 4 * Real.exp (2 * rho))

/-- The physical rectangular regional kernel has one owner-rate certificate
whose constants are independent of `depth`.  CMP89 (2.42) remains the named
representation input; no arbitrary-field action or regional inverse identity
is supplied by the caller. -/
theorem cmp89Eq248PhysicalRegionalOwnerKernelDecayCertificate_draft
    {L K Q : ℕ} [NeZero L] [NeZero K] [NeZero Q]
    (depth : ℕ) {mass a rho : ℝ}
    (ha : 0 ≤ a) (hrho : 0 < rho)
    (hamplitude : rho * Real.exp rho ≤ 1 / 6)
    (hradius : CMP89Eq249UniformNoncentralComplexRadiusCondition rho)
    (hwindow : CMP89Eq249CentralStabilizedComplexWindow a rho)
    (hmass : CMP89Eq251UniformMassWindow mass)
    {m : Fin 4 → ℤ}
    (hm : ∀ mu, 0 < m mu)
    (hside : ∀ mu, ((L ^ (depth + 1) : ℕ) : ℤ) ≤ m mu)
    (hfit : ∀ mu, m mu ≤
      (cmp99SourceSeparatedLargeBlockSide L K depth * (2 * Q) : ℕ))
    {regionalGreen : CMP89SourceNeumannIntegerRectanglePoint m →
      CMP89SourceNeumannIntegerRectanglePoint m → ℂ}
    (R : CMP89NeumannReflectionRepresentationCertificate m regionalGreen
      (cmp89Eq248PhysicalFullLatticeGreen L (depth + 1) mass a)) :
    CMP89RegionalOwnerKernelDecayCertificate regionalGreen
      (fun p =>
        cmp99Eq389SourceLocalizationOwner L K Q depth
          (cmp89SourceNeumannRectanglePointToFinBox_draft hfit p))
      finBoxDist
      (cmp89Eq248PhysicalRegionalUniformOwnerB0_draft a rho) rho := by
  have hbase :
      0 ≤ cmp89Eq248ComplexStabilizedGreenAmplitudeBound_draft a rho :=
    (cmp89Eq248PhysicalFullLatticeGreenDecayCertificate_draft
      (L := L) (j := depth + 1)
      ha hrho hamplitude hradius hwindow hmass).B0_nonneg
  have hden : 0 < 1 - Real.exp (-rho) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  refine ⟨?_, hrho, ?_⟩
  · unfold cmp89Eq248PhysicalRegionalUniformOwnerB0_draft
    exact mul_nonneg
      (mul_nonneg (by positivity) hbase)
      (mul_nonneg (pow_nonneg (div_nonneg (by norm_num) hden.le) _)
        (Real.exp_pos _).le)
  · intro x n
    have hbound :=
      norm_cmp89Eq248PhysicalRegionalGreen_le_physicalOwner_uniform_draft
        depth ha hrho hamplitude hradius hwindow hmass hm hside hfit R x n
    simpa [cmp89Eq248PhysicalRegionalUniformOwnerB0_draft, mul_assoc] using
      hbound

end

end YangMills.RG
