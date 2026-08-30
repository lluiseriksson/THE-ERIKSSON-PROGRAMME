import YangMills.RG.BalabanCMP89NeumannReflectionScaleDictionary

/-!
# CMP89 (2.42): explicit interface for the multiple-reflection representation

PRE-VALIDATION: source is present, its `.olean` has not yet been materialized,
and no result in this module is compiler-verified.

The printed ellipsis in CMP89 (2.42) is represented by one integer translation
index and one reflection parity per coordinate.  This module defines that
series and makes its two actual analytic obligations visible: summability and
equality with the regional Green on the literal source rectangle.

The regional and full-lattice kernels are parameters of the certificate type,
not hidden fields.  Consequently a physical consumer must expose the exact
kernels it identifies.  This interface does not construct either kernel,
prove the equality, choose a finite site count for the inclusive rectangle,
or derive any decay bound.
-/

namespace YangMills.RG

noncomputable section

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

/-- A point of the source block rectangle, using the half-open convention
fixed by CMP89 (1.1). -/
abbrev CMP89SourceNeumannIntegerRectanglePoint (m : Fin d → ℤ) :=
  {n : Fin d → ℤ // n ∈ cmp89SourceNeumannBlockIntegerRectangle m}

/-- The source-shaped multiple-reflection series: an infinite integer
translation vector and one of the `2^d` parity branches. -/
def cmp89NeumannReflectionSeries
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → E)
    (m x n : Fin d → ℤ) : E :=
  ∑' k : Fin d → ℤ,
    ∑ branch : CMP89NeumannReflectionBranch d,
      fullGreen x (cmp89NeumannReflectionImage m n k branch)

/-- Named source gate for CMP89 (2.42).  It ties one explicit regional kernel
to one explicit full-lattice kernel and keeps absolute convergence visible.
-/
structure CMP89NeumannReflectionRepresentationCertificate
    (m : Fin d → ℤ)
    (regionalGreen : CMP89SourceNeumannIntegerRectanglePoint m →
      CMP89SourceNeumannIntegerRectanglePoint m → E)
    (fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → E) where
  summable : ∀ x n : CMP89SourceNeumannIntegerRectanglePoint m,
    Summable (fun k : Fin d → ℤ =>
      ∑ branch : CMP89NeumannReflectionBranch d,
        fullGreen x.1 (cmp89NeumannReflectionImage m n.1 k branch))
  representation : ∀ x n : CMP89SourceNeumannIntegerRectanglePoint m,
    regionalGreen x n =
      cmp89NeumannReflectionSeries fullGreen m x.1 n.1

/-- Projection of the exact printed representation with both kernels visible
in the theorem signature. -/
theorem CMP89NeumannReflectionRepresentationCertificate.eq_series
    {m : Fin d → ℤ}
    {regionalGreen : CMP89SourceNeumannIntegerRectanglePoint m →
      CMP89SourceNeumannIntegerRectanglePoint m → E}
    {fullGreen : (Fin d → ℤ) → (Fin d → ℤ) → E}
    (C : CMP89NeumannReflectionRepresentationCertificate
      m regionalGreen fullGreen)
    (x n : CMP89SourceNeumannIntegerRectanglePoint m) :
    regionalGreen x n =
      cmp89NeumannReflectionSeries fullGreen m x.1 n.1 :=
  C.representation x n

end

end YangMills.RG
