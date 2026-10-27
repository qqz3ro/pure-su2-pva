module

public import KhanSL2.Factorization.ShuffleNaturality
public import Mathlib.Algebra.Lie.TensorProduct

@[expose] public section

/-! Parity on the actual CE chains and its anticommutation with the boundary. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.CEParity
open KhanSL2.LieChains

variable (L M : Type*) [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M]

/-- Parity is exterior parity; coefficient vectors have degree zero. -/
def parity : Module.End ℂ (Chains ℂ L M) :=
  TensorProduct.map (ExteriorShuffle.parity L).toLinearMap LinearMap.id

@[simp] theorem parity_tmul (u : ExteriorAlgebra ℂ L) (m : M) :
    parity L M (u ⊗ₜ[ℂ] m) = ExteriorShuffle.parity L u ⊗ₜ[ℂ] m := rfl

@[simp] theorem parity_parity (z : Chains ℂ L M) : parity L M (parity L M z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u m => simp
  | add z w hz hw => simp only [map_add, hz, hw]

theorem parity_wedge (y : L) (z : Chains ℂ L M) :
    parity L M (wedgeLeft M y z) = -wedgeLeft M y (parity L M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u m =>
    simp only [wedgeLeft_tmul, parity_tmul, map_mul, ExteriorShuffle.parity_ι,
      neg_mul, TensorProduct.neg_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]; abel

variable [LieRingModule L M] [LieModule ℂ L M]

theorem parity_theta (y : L) (z : Chains ℂ L M) :
    parity L M (theta M y z) = theta M y (parity L M z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u m =>
    simp only [theta, lieDeriv_tmul, map_add, parity_tmul,
      ExteriorShuffle.parity_derivExt]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The CE boundary has odd exterior parity. -/
theorem parity_boundary (z : Chains ℂ L M) :
    parity L M (boundary M z) = -boundary M (parity L M z) := by
  induction z using chains_induction with
  | zero => simp
  | one m => simp [boundary_one_tmul]
  | add z w hz hw => simp only [map_add, hz, hw]; abel
  | wedge y z hz =>
    simp only [boundary_wedgeLeft, map_sub, map_neg, parity_theta, parity_wedge, hz]
    abel

/-- An equivalent form convenient for the signed tensor differential. -/
theorem boundary_parity (z : Chains ℂ L M) :
    boundary M (parity L M z) = -parity L M (boundary M z) := by
  rw [parity_boundary, neg_neg]

end KhanSL2.Factorization.CEParity

