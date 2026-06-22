import YangMills.L0_Lattice.FiniteLatticeGeometryInstance

/-!
# Periodic curl/divergence kernel on a finite torus

This file isolates the source-facing finite-difference theorem needed by the
flat physical Poincare path.  The main proposition is deliberately stated for
plain positive-bond fields on `FinBox d N`, with the current ordered plaquette
and backward-divergence conventions.  It carries no Yang--Mills, Hilbert-space,
or Wilson-Hessian terminology.
-/

namespace YangMills.RG

open scoped BigOperators

/-- Source-facing classification theorem for periodic positive-bond fields.

The hypotheses are the ordered plaquette curl stencil and the outgoing-minus-
incoming backward divergence stencil.  The conclusion is direction-wise
constancy. -/
def PeriodicCurlDivKernelClassified
    (d N : ℕ) [NeZero N]
    (V : Type*) [AddCommGroup V] : Prop :=
  ∀ A : FinBox d N → Fin d → V,
    (∀ (x : FinBox d N) (i j : Fin d), i < j →
      A x i
        + A (x.shift i) j
        - A (x.shift j) i
        - A x j = 0) →
    (∀ x : FinBox d N,
      ∑ i : Fin d,
        (A x i - A (x.shiftBack i) i) = 0) →
    ∃ v : Fin d → V,
      ∀ x i, A x i = v i

/-- Forward finite difference in a periodic coordinate direction. -/
def torusForwardDiff {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (i : Fin d) (f : FinBox d N → V) (x : FinBox d N) : V :=
  f (x.shift i) - f x

/-- Backward finite difference in a periodic coordinate direction. -/
def torusBackwardDiff {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (i : Fin d) (f : FinBox d N → V) (x : FinBox d N) : V :=
  f x - f (x.shiftBack i)

/-- Backward divergence of a positive-bond field. -/
def torusDivergence {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (A : FinBox d N → Fin d → V) (x : FinBox d N) : V :=
  ∑ i : Fin d, torusBackwardDiff i (fun y => A y i) x

/-- Periodic scalar Laplacian written as `backward ∘ forward`. -/
def torusLaplacian {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (f : FinBox d N → V) (x : FinBox d N) : V :=
  ∑ i : Fin d, torusBackwardDiff i (torusForwardDiff i f) x

/-- Forward and backward finite differences commute on the periodic torus. -/
theorem torusForwardDiff_torusBackwardDiff_comm
    {d N : ℕ} [NeZero N]
    {V : Type*} [AddCommGroup V]
    (f : FinBox d N → V) (i j : Fin d) (x : FinBox d N) :
    torusForwardDiff i (torusBackwardDiff j f) x =
      torusBackwardDiff j (torusForwardDiff i f) x := by
  simp [torusForwardDiff, torusBackwardDiff, FinBox.shift_shiftBack_comm]
  abel

end YangMills.RG
