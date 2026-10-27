module

public import KhanSL2.BGG.Current

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Coefficient maps and the split constant/positive-current decomposition. -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGG

/-- The coefficient of a homogeneous mode in a polynomial current. -/
def coefficient (n : ℕ) : Current →ₗ[ℂ] G :=
  (TensorProduct.lid ℂ G).toLinearMap.comp ((Polynomial.lcoeff ℂ n).rTensor G)

@[simp] theorem coefficient_tmul (n : ℕ) (p : Polynomial ℂ) (x : G) :
    coefficient n (p ⊗ₜ[ℂ] x) = p.coeff n • x := by
  simp [coefficient]

@[simp] theorem coefficient_mode (n m : ℕ) (x : G) :
    coefficient n (mode m x) = if n = m then x else 0 := by
  simp [Polynomial.coeff_X_pow]

theorem mode_injective (n : ℕ) : Function.Injective (mode n) := by
  intro x y h
  have h' := congrArg (coefficient n) h
  simpa using h'

theorem constant_injective : Function.Injective constant := mode_injective 0

theorem current_zero_lie (u : Current) : ⁅(0 : Current), u⁆ = 0 :=
  (AddMonoidHom.mk' (fun v : Current => ⁅v, u⁆)
    (fun x y => LieRing.add_lie x y u)).map_zero

theorem current_lie_zero (u : Current) : ⁅u, (0 : Current)⁆ = 0 :=
  (AddMonoidHom.mk' (fun v : Current => ⁅u, v⁆)
    (fun x y => LieRing.lie_add u x y)).map_zero
/-- Evaluation at mode zero, a retraction of the constant Lie embedding. -/
def evalZero : Current →ₗ⁅ℂ⁆ G where
  toLinearMap := coefficient 0
  map_lie' := by
    intro u v
    change coefficient 0 ⁅u, v⁆ = ⁅coefficient 0 u, coefficient 0 v⁆
    induction u using TensorProduct.induction_on with
    | zero => simp [current_zero_lie, current_lie_zero]
    | add u w hu hw => simp only [LieRing.add_lie, map_add, hu, hw]
    | tmul p x =>
      induction v using TensorProduct.induction_on with
      | zero => simp [current_zero_lie, current_lie_zero]
      | add v w hv hw => simp only [LieRing.lie_add, map_add, hv, hw]
      | tmul q y =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, coefficient_tmul,
          Polynomial.mul_coeff_zero, smul_lie, lie_smul, smul_smul, mul_comm]

@[simp] theorem evalZero_apply (u : Current) : evalZero u = coefficient 0 u := rfl

@[simp] theorem evalZero_constant (x : G) : evalZero (constant x) = x := by simp

@[simp] theorem evalZero_positive_mode (n : ℕ) (x : G) :
    evalZero (mode (n + 1) x) = 0 := by simp

/-- The ideal of currents with zero constant coefficient. -/
def positive : LieIdeal ℂ Current := evalZero.ker

@[simp] theorem mem_positive (u : Current) : u ∈ positive ↔ coefficient 0 u = 0 := Iff.rfl

/-- A polynomial monomial may be read as a homogeneous current. -/
theorem monomial_tmul (n : ℕ) (a : ℂ) (x : G) :
    (Polynomial.monomial n a) ⊗ₜ[ℂ] x = mode n (a • x) := by
  rw [mode_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Polynomial.smul_X_eq_monomial]

end KhanSL2.BGG