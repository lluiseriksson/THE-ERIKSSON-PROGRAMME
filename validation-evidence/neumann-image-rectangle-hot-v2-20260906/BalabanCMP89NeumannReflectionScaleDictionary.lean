import YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra

/-!
# CMP89 (2.42): lattice-spacing dictionary for the first reflected images

CMP89 printed page 584 writes the geometric rectangle as

`{x in xi Z^d : 0 <= x_mu <= M_mu}`

and displays the first reflected coordinates `-x'_mu-xi` and
`2*M_mu-xi-x'_mu`.  With `x'_mu = xi*n` and `M_mu = xi*m`, these are exactly
the integer reflections `-n-1` and `2*m-1-n` recorded by the orbit-algebra
module.

CMP89 Eq. (1.1), printed page 572, defines every constituent block by the
half-open convention `y_mu <= x_mu < y_mu+1`.  Hence a rectangle built of
unit blocks has integer sites `0 <= n_mu < m_mu`; the inclusive typography on
page 584 is its geometric envelope, not an additional endpoint site.  This
file records both predicates and their inclusion, so no consumer can silently
turn the envelope into `m+1` lattice sites.

It does not identify the Green image series or derive any decay bound.
-/

namespace YangMills.RG

/-- The literal inclusive geometric envelope written on page 584. -/
def cmp89SourceNeumannPrintedInclusiveIntegerRectangle {d : ℕ}
    (m : Fin d → ℤ) :
    Set (Fin d → ℤ) :=
  {n | ∀ mu, 0 ≤ n mu ∧ n mu ≤ m mu}

theorem mem_cmp89SourceNeumannPrintedInclusiveIntegerRectangle_iff {d : ℕ}
    {m n : Fin d → ℤ} :
    n ∈ cmp89SourceNeumannPrintedInclusiveIntegerRectangle m ↔
      ∀ mu, 0 ≤ n mu ∧ n mu ≤ m mu := by
  rfl

/-- The source-faithful lattice carrier inherited from the half-open block
definition (1.1): exactly `m_mu` sites in coordinate `mu`. -/
def cmp89SourceNeumannBlockIntegerRectangle {d : ℕ} (m : Fin d → ℤ) :
    Set (Fin d → ℤ) :=
  {n | ∀ mu, 0 ≤ n mu ∧ n mu < m mu}

theorem mem_cmp89SourceNeumannBlockIntegerRectangle_iff {d : ℕ}
    {m n : Fin d → ℤ} :
    n ∈ cmp89SourceNeumannBlockIntegerRectangle m ↔
      ∀ mu, 0 ≤ n mu ∧ n mu < m mu := by
  rfl

/-- Positive side lengths make the half-open source carrier genuinely
inhabited; the zero lattice site is an explicit witness. -/
theorem cmp89SourceNeumannBlockIntegerRectangle_zero_mem
    {d : ℕ} {m : Fin d → ℤ} (hm : ∀ mu, 0 < m mu) :
    (0 : Fin d → ℤ) ∈ cmp89SourceNeumannBlockIntegerRectangle m := by
  intro mu
  exact ⟨le_rfl, hm mu⟩

/-- Every actual block site lies in the printed inclusive envelope; the
converse would add the spurious upper-endpoint site. -/
theorem cmp89SourceNeumannBlockIntegerRectangle_subset_printedInclusive
    {d : ℕ} {m : Fin d → ℤ} :
    cmp89SourceNeumannBlockIntegerRectangle m ⊆
      cmp89SourceNeumannPrintedInclusiveIntegerRectangle m := by
  intro n hn mu
  exact ⟨(hn mu).1, (hn mu).2.le⟩

/-- The lower integer reflection is exactly the printed physical coordinate
`-x'-xi`. -/
theorem cmp89NeumannLeftReflection_spacing_dictionary
    (spacing : ℝ) (n : ℤ) :
    spacing * (cmp89NeumannLeftReflection n : ℝ) =
      -(spacing * (n : ℝ)) - spacing := by
  simp [cmp89NeumannLeftReflection]
  ring

/-- Before identifying `M`, the upper integer reflection has the exact
scaled form `2*(xi*m)-xi-x'`. -/
theorem cmp89NeumannRightReflection_spacing_dictionary
    (spacing : ℝ) (m n : ℤ) :
    spacing * (cmp89NeumannRightReflection m n : ℝ) =
      2 * (spacing * (m : ℝ)) - spacing - spacing * (n : ℝ) := by
  simp [cmp89NeumannRightReflection]
  ring

/-- With the visible source dictionary `M = xi*m`, the upper reflection is
literally `2*M-xi-x'`. -/
theorem cmp89NeumannRightReflection_physical_dictionary
    (spacing M : ℝ) (m n : ℤ)
    (hM : M = spacing * (m : ℝ)) :
    spacing * (cmp89NeumannRightReflection m n : ℝ) =
      2 * M - spacing - spacing * (n : ℝ) := by
  rw [hM]
  exact cmp89NeumannRightReflection_spacing_dictionary spacing m n

/-- Coordinatewise form of the lower printed image. -/
theorem cmp89NeumannLeftReflectionImage_spacing_dictionary {d : ℕ}
    (spacing : ℝ) (n : Fin d → ℤ) (mu : Fin d) :
    spacing * (cmp89NeumannLeftReflection (n mu) : ℝ) =
      -(spacing * (n mu : ℝ)) - spacing :=
  cmp89NeumannLeftReflection_spacing_dictionary spacing (n mu)

/-- Coordinatewise form of the upper printed image. -/
theorem cmp89NeumannRightReflectionImage_physical_dictionary {d : ℕ}
    (spacing : ℝ) (M : Fin d → ℝ) (m n : Fin d → ℤ)
    (hM : ∀ mu, M mu = spacing * (m mu : ℝ)) (mu : Fin d) :
    spacing * (cmp89NeumannRightReflection (m mu) (n mu) : ℝ) =
      2 * M mu - spacing - spacing * (n mu : ℝ) :=
  cmp89NeumannRightReflection_physical_dictionary
    spacing (M mu) (m mu) (n mu) (hM mu)

end YangMills.RG
