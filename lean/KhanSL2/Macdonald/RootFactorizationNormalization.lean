module

public import KhanSL2.SymmetricFamily.BlockAverageNormalization
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The precise scalar relating normalized coefficient factorization and
primitive odd/even root factorization is invertible on every admissible block. -/
noncomputable section
namespace KhanSL2.Macdonald

/-- Normalize the coefficient coproduct once and retain both primitive root factors. -/
def rootFactorizationNormalization (q r q₁ r₁ : ℕ) : ℂ :=
  (Nat.choose (q+2*r) (q₁+2*r₁) : ℂ)⁻¹ *
    (Nat.choose q q₁ : ℂ) * (Nat.choose r r₁ : ℂ)

theorem rootFactorizationNormalization_ne_zero {q r q₁ r₁ : ℕ}
    (hq : q₁ ≤ q) (hr : r₁ ≤ r) : rootFactorizationNormalization q r q₁ r₁ ≠ 0 := by
  have hq' : (Nat.choose q q₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos hq))
  have hr' : (Nat.choose r r₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos hr))
  have ht : q₁+2*r₁ ≤ q+2*r := by omega
  have ht' : (Nat.choose (q+2*r) (q₁+2*r₁) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos ht))
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero ht') hq') hr'

variable (A : Type*) [CommRing A] [Algebra ℂ A]
variable (M : Type*) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]

/-- A nonzero complex normalization is invertible over any complex coefficient
algebra, including nonreduced and zero algebras. -/
def complexNormalizationEquiv (c : ℂ) (hc : c ≠ 0) : M ≃ₗ[A] M where
  toFun (x : M) := c • x
  invFun (x : M) := c⁻¹ • x
  left_inv x := by
    change c⁻¹ • (c • x) = x
    rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
  right_inv x := by
    change c • (c⁻¹ • x) = x
    rw [smul_smul,mul_inv_cancel₀ hc,one_smul]
  map_add' x y := smul_add c x y
  map_smul' a x := smul_comm c a x

@[simp] theorem complexNormalizationEquiv_apply (c : ℂ) (hc : c ≠ 0) (x : M) :
    complexNormalizationEquiv A M c hc x = c • x := rfl

/-- The exact odd/even normalization gives an automorphism of every actual chart module. -/
def rootFactorizationNormalizationEquiv {q r q₁ r₁ : ℕ} (hq : q₁ ≤ q) (hr : r₁ ≤ r) :
    M ≃ₗ[A] M := complexNormalizationEquiv A M (rootFactorizationNormalization q r q₁ r₁)
      (rootFactorizationNormalization_ne_zero hq hr)

end KhanSL2.Macdonald
