module

public import KhanSL2.Factorization.ShuffleRelativeDifferential
public import KhanSL2.Factorization.ShuffleCoefficientNaturality
public import KhanSL2.Factorization.CoefficientMaps

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Naturality of the actual relative CE shuffle in both coefficient factors. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.BGGBridge KhanSL2.Current

variable {M N M' N' : Type*}
  [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [AddCommGroup M'] [Module ℂ M'] [AddCommGroup N'] [Module ℂ N']

/-- The fixed exterior comparison is natural in its coefficient space. -/
theorem rawMap_J (f : M →ₗ[ℂ] M') (z : LieChains.Chains ℂ plus M) :
    rawMap f (CEModel.J z) =
      CEModel.J (LinearMap.lTensor (ExteriorAlgebra ℂ plus) f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u m => rfl
  | add z w hz hw => simp only [map_add, hz, hw]

theorem tensorModelEquiv_coeffMap (f : M →ₗ[ℂ] M') (g : N →ₗ[ℂ] N')
    (z : CETensor.TensorChains plus M N) :
    tensorModelEquiv M' N'
      (TensorProduct.map (LinearMap.lTensor (ExteriorAlgebra ℂ plus) f)
        (LinearMap.lTensor (ExteriorAlgebra ℂ plus) g) z) =
      TensorProduct.map (rawMap f) (rawMap g) (tensorModelEquiv M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    simp only [TensorProduct.map_tmul, tensorModelEquiv_tmul, rawMap_J]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- Naturality holds for the actual transported chain map before quotienting. -/
theorem rawShuffle_coeffMap (f : M →ₗ[ℂ] M') (g : N →ₗ[ℂ] N')
    (z : RawChains (M ⊗[ℂ] N)) :
    rawShuffle M' N' (rawMap (TensorProduct.map f g) z) =
      TensorProduct.map (rawMap f) (rawMap g) (rawShuffle M N z) := by
  obtain ⟨u, rfl⟩ := (CEModel.J (N := M ⊗[ℂ] N)).surjective z
  rw [rawMap_J, rawShuffle_J, rawShuffle_J, CEShuffle.shuffle_coeffMap,
    tensorModelEquiv_coeffMap]

variable [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
  [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
  [LieRingModule BGG.Current M'] [LieModule ℂ BGG.Current M']
  [LieRingModule BGG.Current N'] [LieModule ℂ BGG.Current N']

/-- Constant equivariance is preserved by tensoring coefficient maps. -/
theorem ConstantEquivariant.tensorMap {f : M →ₗ[ℂ] M'} {g : N →ₗ[ℂ] N'}
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g) :
    ConstantEquivariant (TensorProduct.map f g) := by
  intro x z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul m n =>
    simp only [TensorProduct.LieModule.lie_tmul_right, map_add, TensorProduct.map_tmul,
      hf x m, hg x n]
  | add z w hz hw => simp only [lie_add, map_add, hz, hw]

/-- Quotient projection is natural for the two constant-equivariant coefficient maps. -/
theorem projectRelativeTensor_coeffMap (f : M →ₗ[ℂ] M') (g : N →ₗ[ℂ] N')
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g)
    (z : RawChains M ⊗[ℂ] RawChains N) :
    projectRelativeTensor M' N' (TensorProduct.map (rawMap f) (rawMap g) z) =
      TensorProduct.map (coefficientMap f hf) (coefficientMap g hg)
        (projectRelativeTensor M N z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => rfl
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The specified relative shuffle is natural on the actual coinvariant quotients. -/
theorem relativeShuffle_coeffMap (f : M →ₗ[ℂ] M') (g : N →ₗ[ℂ] N')
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g)
    (z : RelativeChains (M ⊗[ℂ] N)) :
    relativeShuffle M' N'
      (coefficientMap (TensorProduct.map f g) (hf.tensorMap hg) z) =
      TensorProduct.map (coefficientMap f hf) (coefficientMap g hg)
        (relativeShuffle M N z) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective (relC (M ⊗[ℂ] N)) z
  change projectRelativeTensor M' N' (rawShuffle M' N' (rawMap (TensorProduct.map f g) u)) =
    TensorProduct.map (coefficientMap f hf) (coefficientMap g hg)
      (projectRelativeTensor M N (rawShuffle M N u))
  rw [rawShuffle_coeffMap, projectRelativeTensor_coeffMap]

end KhanSL2.Factorization
