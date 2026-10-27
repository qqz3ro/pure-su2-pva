module

public import KhanSL2.Factorization.ShuffleTensorDifferential

@[expose] public section

/-! The canonical CE shuffle is an actual chain map for tensor coefficients. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.CEShuffle
open KhanSL2.LieChains

variable (L M N : Type*) [LieRing L] [LieAlgebra ℂ L]
  [AddCommGroup M] [Module ℂ M] [LieRingModule L M] [LieModule ℂ L M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule L N] [LieModule ℂ L N]

/-- Regroup two exterior factors with their respective coefficient factors. -/
def reorder : (ExteriorShuffle.Tensor L ⊗[ℂ] (M ⊗[ℂ] N)) ≃ₗ[ℂ]
    CETensor.TensorChains L M N :=
  TensorProduct.tensorTensorTensorComm ℂ (ExteriorAlgebra ℂ L) (ExteriorAlgebra ℂ L) M N

omit [LieRingModule L M] [LieModule ℂ L M] [LieRingModule L N] [LieModule ℂ L N] in
@[simp] theorem reorder_tmul (u v : ExteriorAlgebra ℂ L) (m : M) (n : N) :
    reorder L M N ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (m ⊗ₜ[ℂ] n)) =
      (u ⊗ₜ[ℂ] m) ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] n) := rfl

/-- The specified shuffle on actual CE chains, using the genuine exterior coproduct. -/
def shuffle : Chains ℂ L (M ⊗[ℂ] N) →ₗ[ℂ] CETensor.TensorChains L M N :=
  (reorder L M N).toLinearMap.comp
    (TensorProduct.map (ExteriorShuffle.shuffle L) LinearMap.id)

omit [LieRingModule L M] [LieModule ℂ L M] [LieRingModule L N] [LieModule ℂ L N] in
@[simp] theorem shuffle_tmul (u : ExteriorAlgebra ℂ L) (t : M ⊗[ℂ] N) :
    shuffle L M N (u ⊗ₜ[ℂ] t) = reorder L M N (ExteriorShuffle.shuffle L u ⊗ₜ[ℂ] t) := rfl

omit [LieRingModule L M] [LieModule ℂ L M] [LieRingModule L N] [LieModule ℂ L N] in
@[simp] theorem shuffle_one_tmul (m : M) (n : N) :
    shuffle L M N ((1 : ExteriorAlgebra ℂ L) ⊗ₜ[ℂ] (m ⊗ₜ[ℂ] n)) =
      ((1 : ExteriorAlgebra ℂ L) ⊗ₜ[ℂ] m) ⊗ₜ[ℂ]
        ((1 : ExteriorAlgebra ℂ L) ⊗ₜ[ℂ] n) := by
  rw [shuffle_tmul, ExteriorShuffle.shuffle_one, reorder_tmul]

omit [LieRingModule L M] [LieModule ℂ L M] [LieRingModule L N] [LieModule ℂ L N] in
private theorem reorder_create (y : L) (z : ExteriorShuffle.Tensor L) (t : M ⊗[ℂ] N) :
    reorder L M N (ExteriorShuffle.create L y z ⊗ₜ[ℂ] t) =
      CETensor.create L M N y (reorder L M N (z ⊗ₜ[ℂ] t)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      simp only [ExteriorShuffle.create_tmul, TensorProduct.add_tmul, map_add,
        reorder_tmul, CETensor.create_tmul, wedgeLeft_tmul, CEParity.parity_tmul]
    | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs]
  | add z w hz hw => simp only [map_add, TensorProduct.add_tmul, hz, hw]

omit [LieRingModule L M] [LieModule ℂ L M] [LieRingModule L N] [LieModule ℂ L N] in
/-- The shuffle intertwines creation with its signed diagonal counterpart. -/
theorem shuffle_wedge (y : L) (z : Chains ℂ L (M ⊗[ℂ] N)) :
    shuffle L M N (wedgeLeft (M ⊗[ℂ] N) y z) =
      CETensor.create L M N y (shuffle L M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u t =>
    rw [wedgeLeft_tmul, shuffle_tmul, shuffle_tmul,
      ExteriorShuffle.shuffle_ι_mul, reorder_create]
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem reorder_action (y : L) (z : ExteriorShuffle.Tensor L) (t : M ⊗[ℂ] N) :
    reorder L M N (ExteriorShuffle.tensorDeriv (LieModule.toEnd ℂ L L y) z ⊗ₜ[ℂ] t +
      z ⊗ₜ[ℂ] ⁅y, t⁆) = CETensor.action L M N y (reorder L M N (z ⊗ₜ[ℂ] t)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      simp only [ExteriorShuffle.tensorDeriv_tmul, TensorProduct.add_tmul,
        TensorProduct.LieModule.lie_tmul_right, TensorProduct.tmul_add, map_add,
        reorder_tmul, CETensor.action_tmul, theta, lieDeriv_tmul]
      abel
    | add t s ht hs =>
      simp only [lie_add, TensorProduct.tmul_add, map_add] at ht hs ⊢
      rw [← ht, ← hs]
      abel
  | add z w hz hw =>
    simp only [map_add, TensorProduct.add_tmul] at hz hw ⊢
    rw [← hz, ← hw]
    abel
/-- The shuffle intertwines the actual diagonal Lie derivatives. -/
theorem shuffle_theta (y : L) (z : Chains ℂ L (M ⊗[ℂ] N)) :
    shuffle L M N (theta (M ⊗[ℂ] N) y z) =
      CETensor.action L M N y (shuffle L M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u t =>
    change shuffle L M N (derivExt (LieModule.toEnd ℂ L L y) u ⊗ₜ[ℂ] t +
      u ⊗ₜ[ℂ] ⁅y, t⁆) = _
    rw [map_add, shuffle_tmul, shuffle_tmul, shuffle_tmul, ExteriorShuffle.shuffle_derivExt]
    simpa only [map_add] using reorder_action L M N y (ExteriorShuffle.shuffle L u) t
  | add z w hz hw => simp only [map_add, hz, hw]

private theorem differential_shuffle_one (t : M ⊗[ℂ] N) :
    CETensor.differential L M N (shuffle L M N ((1 : ExteriorAlgebra ℂ L) ⊗ₜ[ℂ] t)) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    rw [shuffle_one_tmul, CETensor.differential_tmul, boundary_one_tmul, boundary_one_tmul]
    simp
  | add t s ht hs => simp only [TensorProduct.tmul_add, map_add, ht, hs, add_zero]

/-- The canonical shuffle is a chain map for the actual CE boundaries. -/
theorem shuffle_boundary (z : Chains ℂ L (M ⊗[ℂ] N)) :
    shuffle L M N (boundary (M ⊗[ℂ] N) z) =
      CETensor.differential L M N (shuffle L M N z) := by
  induction z using chains_induction with
  | zero => simp
  | one t => rw [boundary_one_tmul, map_zero, differential_shuffle_one]
  | add z w hz hw => simp only [map_add, hz, hw]
  | wedge y z hz =>
    rw [boundary_wedgeLeft, map_sub, map_neg, shuffle_theta, shuffle_wedge,
      shuffle_wedge, CETensor.differential_create, hz]

end KhanSL2.Factorization.CEShuffle

