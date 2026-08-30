import YangMills.RG.BalabanCMP89NeumannReflectionOrbitAlgebra

/-!
# CMP89 (2.42): lattice-spacing dictionary for the first reflected images

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and no result in this module is compiler-verified.

CMP89 printed page 584 writes the source rectangle as

`{x in xi Z^d : 0 <= x_mu <= M_mu}`

and displays the first reflected coordinates `-x'_mu-xi` and
`2*M_mu-xi-x'_mu`.  With `x'_mu = xi*n` and `M_mu = xi*m`, these are exactly
the integer reflections `-n-1` and `2*m-1-n` recorded by the orbit-algebra
module.

This file records that scaling identity and the literal inclusive integer
rectangle only.  It does not infer the period of the ellipsis in (2.42),
identify the Green image series, or resolve whether a later finite-index
implementation should count `m` or `m+1` sites.
-/

namespace YangMills.RG

/-- The literal inclusive integer rectangle obtained from the printed
condition `0 <= x_mu <= M_mu` after writing `x = xi*n`, `M = xi*m`. -/
def cmp89SourceNeumannIntegerRectangle {d : ℕ} (m : Fin d → ℤ) :
    Set (Fin d → ℤ) :=
  {n | ∀ mu, 0 ≤ n mu ∧ n mu ≤ m mu}

theorem mem_cmp89SourceNeumannIntegerRectangle_iff {d : ℕ}
    {m n : Fin d → ℤ} :
    n ∈ cmp89SourceNeumannIntegerRectangle m ↔
      ∀ mu, 0 ≤ n mu ∧ n mu ≤ m mu := by
  rfl

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
