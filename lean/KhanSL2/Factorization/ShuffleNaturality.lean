module

public import KhanSL2.Factorization.ShuffleExterior

@[expose] public section

/-! Naturality and derivation equivariance of the canonical exterior shuffle. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.ExteriorShuffle
open KhanSL2.LieChains

variable {L M : Type*} [AddCommGroup L] [Module ℂ L]
  [AddCommGroup M] [Module ℂ M]

theorem parity_map (f : L →ₗ[ℂ] M) (u : Ext L) :
    parity M (ExteriorAlgebra.map f u) = ExteriorAlgebra.map f (parity L u) := by
  have h : (parity M).comp (ExteriorAlgebra.map f) =
      (ExteriorAlgebra.map f).comp (parity L) := by
    ext y
    simp
  exact AlgHom.congr_fun h u

/-- Apply the same linear map to both exterior factors. -/
def tensorMap (f : L →ₗ[ℂ] M) : Tensor L →ₗ[ℂ] Tensor M :=
  TensorProduct.map (ExteriorAlgebra.map f).toLinearMap (ExteriorAlgebra.map f).toLinearMap

@[simp] theorem tensorMap_tmul (f : L →ₗ[ℂ] M) (u v : Ext L) :
    tensorMap f (u ⊗ₜ[ℂ] v) = ExteriorAlgebra.map f u ⊗ₜ[ℂ] ExteriorAlgebra.map f v := rfl

theorem tensorMap_create (f : L →ₗ[ℂ] M) (y : L) (z : Tensor L) :
    tensorMap f (create L y z) = create M (f y) (tensorMap f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    simp only [create_tmul, map_add, tensorMap_tmul, map_mul,
      ExteriorAlgebra.map_apply_ι, parity_map]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The actual shuffle commutes with every linear map on generators. -/
theorem shuffle_map (f : L →ₗ[ℂ] M) (u : Ext L) :
    shuffle M (ExteriorAlgebra.map f u) = tensorMap f (shuffle L u) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one,
      shuffle_one, tensorMap_tmul]
  | add u v hu hv => simp only [map_add, hu, hv]
  | ι_mul u y hu =>
    rw [map_mul, ExteriorAlgebra.map_apply_ι, shuffle_ι_mul,
      shuffle_ι_mul, tensorMap_create, hu]

/-- Exterior endomorphism derivations preserve parity. -/
theorem parity_derivExt (D : Module.End ℂ L) (u : Ext L) :
    parity L (derivExt D u) = derivExt D (parity L u) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | ι_mul u y hu =>
    simp only [derivExt_ι_mul, map_add, map_mul, parity_ι, neg_mul,
      map_neg, derivExt_ι_mul, hu, neg_add_rev]
    abel

/-- The diagonal extension of a generator endomorphism to the exterior tensor square. -/
def tensorDeriv (D : Module.End ℂ L) : Module.End ℂ (Tensor L) :=
  LinearMap.rTensor (Ext L) (derivExt D) + LinearMap.lTensor (Ext L) (derivExt D)

@[simp] theorem tensorDeriv_tmul (D : Module.End ℂ L) (u v : Ext L) :
    tensorDeriv D (u ⊗ₜ[ℂ] v) = derivExt D u ⊗ₜ[ℂ] v + u ⊗ₜ[ℂ] derivExt D v := rfl

theorem tensorDeriv_create (D : Module.End ℂ L) (y : L) (z : Tensor L) :
    tensorDeriv D (create L y z) =
      create L y (tensorDeriv D z) + create L (D y) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    simp only [create_tmul, tensorDeriv_tmul, map_add, derivExt_ι_mul,
      TensorProduct.add_tmul, TensorProduct.tmul_add, parity_derivExt]
    abel
  | add z w hz hw => simp only [map_add, hz, hw]; abel

/-- The actual shuffle intertwines every extended derivation, hence all constant Lie actions. -/
theorem shuffle_derivExt (D : Module.End ℂ L) (u : Ext L) :
    shuffle L (derivExt D u) = tensorDeriv D (shuffle L u) := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [derivExt_algebraMap, map_zero, Algebra.algebraMap_eq_smul_one,
      map_smul, map_smul, shuffle_one, tensorDeriv_tmul]
    simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | ι_mul u y hu =>
    rw [derivExt_ι_mul, map_add, shuffle_ι_mul, shuffle_ι_mul,
      shuffle_ι_mul, tensorDeriv_create, hu]
    abel

end KhanSL2.Factorization.ExteriorShuffle

