module

public import KhanSL2.ExteriorParity
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Hom

@[expose] public section

/-! Ring and algebra structures for the explicit finite exterior product. -/

noncomputable section

namespace KhanSL2.FiniteExterior

class GeneratorOrder (α : Type*) where
  code : α → ℕ
  code_injective : Function.Injective code

variable {α : Type*} [DecidableEq α] [GeneratorOrder α]

instance : Ring (Exterior α) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (Finset α →₀ ℂ))
  mul := wedge GeneratorOrder.code
  one := monomial ∅
  mul_assoc := wedge_assoc _
  one_mul := wedge_one_left _
  mul_one := wedge_one_right _
  zero_mul := wedge_zero_left _
  mul_zero := wedge_zero_right _
  left_distrib := wedge_add_right _
  right_distrib := wedge_add_left _
  natCast n := Finsupp.single ∅ (n : ℂ)
  natCast_zero := by simp
  natCast_succ n := by
    change Finsupp.single ∅ ((n + 1 : ℕ) : ℂ) =
      Finsupp.single ∅ (n : ℂ) + Finsupp.single ∅ 1
    simp [Finsupp.single_add]
  intCast n := Finsupp.single ∅ (n : ℂ)
  intCast_ofNat n := by
    change Finsupp.single ∅ ((n : ℤ) : ℂ) = Finsupp.single ∅ (n : ℂ)
    simp
  intCast_negSucc n := by
    change Finsupp.single ∅ ((Int.negSucc n : ℤ) : ℂ) =
      - Finsupp.single ∅ ((n + 1 : ℕ) : ℂ)
    simp [Int.cast_negSucc, Finsupp.single_neg, Finsupp.single_add]

theorem mul_def (u v : Exterior α) :
    u * v = wedge GeneratorOrder.code u v := rfl

theorem one_def : (1 : Exterior α) = monomial ∅ := rfl

instance : Algebra ℂ (Exterior α) where
  algebraMap := {
    toFun := Finsupp.single ∅
    map_one' := rfl
    map_mul' := fun a b => by
      change Finsupp.single ∅ (a * b) =
        wedge GeneratorOrder.code (Finsupp.single ∅ a) (Finsupp.single ∅ b)
      simp [monomialWedge, monomial]
    map_zero' := by simp
    map_add' := fun a b => Finsupp.single_add ∅ a b }
  commutes' r u := by
    change wedge GeneratorOrder.code (Finsupp.single ∅ r) u =
      wedge GeneratorOrder.code u (Finsupp.single ∅ r)
    have hr : Finsupp.single ∅ r = r • monomial (∅ : Finset α) := by simp [monomial]
    rw [hr, wedge_smul_left, wedge_smul_right, wedge_one_left, wedge_one_right]
  smul_def' r u := by
    change r • u = wedge GeneratorOrder.code (Finsupp.single ∅ r) u
    have hr : Finsupp.single ∅ r = r • monomial (∅ : Finset α) := by simp [monomial]
    rw [hr, wedge_smul_left, wedge_one_left]

def parity : Exterior α →ₐ[ℂ] Exterior α where
  toFun := parityLinear
  map_zero' := map_zero parityLinear
  map_add' := map_add parityLinear
  map_one' := parity_one
  map_mul' := parity_wedge _
  commutes' r := by
    change parityLinear (Finsupp.single ∅ r) = Finsupp.single ∅ r
    simp

theorem parity_apply (u : Exterior α) : parity u = parityLinear u := rfl

end KhanSL2.FiniteExterior

