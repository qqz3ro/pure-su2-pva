module

public import KhanSL2.BGG.CurrentPositive

@[expose] public section

/-! Polynomial dilation and its homogeneous action on positive currents. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG

/-- Dilation of the current variable: a mode of degree `n` is multiplied by `t^n`. -/
def currentScale (t : ℂ) : Current →ₗ⁅ℂ⁆ Current :=
  LieAlgebra.ExtendScalars.map
    (Polynomial.aeval (Polynomial.C t * Polynomial.X)) (LieHom.id : G →ₗ⁅ℂ⁆ G)

@[simp] theorem currentScale_mode (t : ℂ) (n : ℕ) (x : G) :
    currentScale t (mode n x) = (t ^ n) • mode n x := by
  simp only [mode_apply, currentScale, LieAlgebra.ExtendScalars.map_apply_tmul,
    LieHom.id_apply, map_pow, Polynomial.aeval_X, mul_pow]
  rw [← Polynomial.C_pow]
  rw [← Polynomial.smul_eq_C_mul, TensorProduct.smul_tmul']

/-- Dilation fixes the constant coefficient of every polynomial current. -/
@[simp] theorem evalZero_currentScale (t : ℂ) (u : Current) :
    evalZero (currentScale t u) = evalZero u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul p x =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [TensorProduct.add_tmul, map_add, hp, hq]
    | monomial n a =>
      rw [monomial_tmul, currentScale_mode, map_smul]
      cases n with
      | zero => simp
      | succ n => simp

/-- Dilation restricts to the genuine ideal of positive currents. -/
def positiveScale (t : ℂ) : positive →ₗ⁅ℂ⁆ positive where
  toFun u := ⟨currentScale t u, by
    change evalZero (currentScale t u) = 0
    rw [evalZero_currentScale]
    exact u.property⟩
  map_add' u v := Subtype.ext (map_add (currentScale t) (u : Current) (v : Current))
  map_smul' r u := Subtype.ext (map_smul (currentScale t) r (u : Current))
  map_lie' {u v} := Subtype.ext ((currentScale t).map_lie (u : Current) (v : Current))

@[simp] theorem positiveScale_coe (t : ℂ) (u : positive) :
    (positiveScale t u : Current) = currentScale t u := rfl

@[simp] theorem positiveScale_mode (t : ℂ) (n : ℕ) (x : G) :
    positiveScale t (positiveMode n x) = (t ^ (n + 1)) • positiveMode n x := by
  apply Subtype.ext
  exact currentScale_mode t (n + 1) x

end KhanSL2.BGG
