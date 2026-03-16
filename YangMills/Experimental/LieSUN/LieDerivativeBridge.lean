import Mathlib
import YangMills.Experimental.LieSUN.LieDerivativeDef
import YangMills.Experimental.LieSUN.LieExpCurve

/-!
# LieDerivativeBridge — Abstract theorems

Firmas exactas confirmadas:
- lieDerivativeVia (curve : G → ℝ → G) (f : G → ℝ) (U : G) : ℝ
- lieExpCurve N_c X hX htr (U : SUN) (t : ℝ) : SUN
  i.e. lieExpCurve N_c X hX htr : SUN → ℝ → SUN  ← esto es curve : G → ℝ → G ✅

Conexión: lieDerivativeVia (lieExpCurve N_c X hX htr) f U
                                     ↑ ya tiene la forma G → ℝ → G

Build cycle con P8: documentado. Bridge autónomo.
-/

open scoped Matrix

section LieDerivativeBridge

variable {k : ℕ} [NeZero k]

open YangMills.Experimental.LieSUN

/-- Concrete Lie derivative: d/dt|₀ f(U·exp(t·X)) -/
noncomputable def lieDerivExp
    (X : Matrix (Fin k) (Fin k) ℂ) (hX : Xᴴ = -X) (htr : X.trace = 0)
    (f : ↥(Matrix.specialUnitaryGroup (Fin k) ℂ) → ℝ)
    (U : ↥(Matrix.specialUnitaryGroup (Fin k) ℂ)) : ℝ :=
  lieDerivativeVia (lieExpCurve k X hX htr) f U

/-- L_X(const c) = 0 — unconditional. -/
theorem lieDerivExp_const
    (X : Matrix (Fin k) (Fin k) ℂ) (hX : Xᴴ = -X) (htr : X.trace = 0)
    (c : ℝ) (U : ↥(Matrix.specialUnitaryGroup (Fin k) ℂ)) :
    lieDerivExp X hX htr (fun _ => c) U = 0 :=
  lieDerivativeVia_const (lieExpCurve k X hX htr) c U

/-- L_X(f+g) = L_X f + L_X g. -/
theorem lieDerivExp_add
    (X : Matrix (Fin k) (Fin k) ℂ) (hX : Xᴴ = -X) (htr : X.trace = 0)
    (f g : ↥(Matrix.specialUnitaryGroup (Fin k) ℂ) → ℝ)
    (U : ↥(Matrix.specialUnitaryGroup (Fin k) ℂ))
    (hf : DifferentiableAt ℝ (fun t => f (lieExpCurve k X hX htr U t)) 0)
    (hg : DifferentiableAt ℝ (fun t => g (lieExpCurve k X hX htr U t)) 0) :
    lieDerivExp X hX htr (fun x => f x + g x) U =
      lieDerivExp X hX htr f U + lieDerivExp X hX htr g U :=
  lieDerivativeVia_add (lieExpCurve k X hX htr) f g U hf hg

/-- L_X(c*f) = c * L_X f. -/
theorem lieDerivExp_smul
    (X : Matrix (Fin k) (Fin k) ℂ) (hX : Xᴴ = -X) (htr : X.trace = 0)
    (c : ℝ) (f : ↥(Matrix.specialUnitaryGroup (Fin k) ℂ) → ℝ)
    (U : ↥(Matrix.specialUnitaryGroup (Fin k) ℂ))
    (hf : DifferentiableAt ℝ (fun t => f (lieExpCurve k X hX htr U t)) 0) :
    lieDerivExp X hX htr (fun x => c * f x) U =
      c * lieDerivExp X hX htr f U :=
  lieDerivativeVia_smul (lieExpCurve k X hX htr) f c U hf

end LieDerivativeBridge
