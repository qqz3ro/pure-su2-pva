module

public import KhanSL2.Macdonald.Basic
public import Mathlib.Algebra.MvPolynomial.Derivation

@[expose] public section

/-! The coefficient-lowering derivation on the concrete mixed algebra.
It acts only on the symmetric variables. The later CE pairing will identify
this operator with the transpose of multiplication by a root power sum. -/

noncomputable section
open scoped BigOperators TensorProduct

namespace KhanSL2.Macdonald

/-- Lower one even mode by m, with zero below the lower boundary. -/
def polynomialShift (m : ℕ) : Derivation ℂ Poly Poly :=
  MvPolynomial.mkDerivation ℂ (fun i : Mode =>
    if m ≤ i.index then MvPolynomial.X (⟨i.index - m, i.color⟩ : Mode) else 0)

@[simp] theorem polynomialShift_X (m n : ℕ) (a : Fin 3) :
    polynomialShift m (MvPolynomial.X (⟨n, a⟩ : Mode)) =
      if m ≤ n then MvPolynomial.X (⟨n-m, a⟩ : Mode) else 0 :=
  MvPolynomial.mkDerivation_X _ _ _

/-- Differentiate the polynomial factor, leaving the exterior factor in each term unchanged. -/
def coefficientShift (m : ℕ) : Module.End ℂ W :=
  TensorProduct.map (polynomialShift m).toLinearMap LinearMap.id

@[simp] theorem coefficientShift_tmul (m : ℕ) (p : Poly) (u : Exterior) :
    coefficientShift m (p ⊗ₜ[ℂ] u) = polynomialShift m p ⊗ₜ[ℂ] u := rfl

@[simp] theorem coefficientShift_sigma (m : ℕ) (a : Fin 3) (n : ℕ) :
    coefficientShift m (sigma a n) = if m ≤ n then sigma a (n-m) else 0 := by
  simp only [sigma, coefficientShift_tmul, polynomialShift_X]
  split <;> simp

@[simp] theorem coefficientShift_psi (m : ℕ) (a : Fin 3) (i : ℕ) :
    coefficientShift m (psi a i) = 0 := by
  simp [psi]

@[simp] theorem coefficientShift_one (m : ℕ) : coefficientShift m 1 = 0 := by
  simp [Algebra.TensorProduct.one_def]

/-- The genuine Leibniz rule on the whole mixed algebra. -/
theorem coefficientShift_mul (m : ℕ) (u v : W) :
    coefficientShift m (u * v) = coefficientShift m u * v + u * coefficientShift m v := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul p x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q y =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, coefficientShift_tmul,
        Derivation.leibniz, smul_eq_mul, TensorProduct.add_tmul]
      rw [mul_comm q (polynomialShift m p)]
      abel
    | add v w hv hw => simp only [mul_add, map_add, hv, hw, add_mul]; abel
  | add u w hu hw => simp only [add_mul, map_add, hu, hw, mul_add]; abel

end KhanSL2.Macdonald
