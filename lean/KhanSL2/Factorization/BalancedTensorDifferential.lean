module

public import KhanSL2.Factorization.BalancedTensorModel
public import KhanSL2.Factorization.ShuffleParityDegree
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The signed relative tensor boundary is the differential of the genuine
categorical tensor complex on every homogeneous degree sum. -/

noncomputable section
open scoped TensorProduct
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

/-- Forgetting homogeneous degree intertwines the categorical tensor differential
with the actual signed relative tensor boundary. -/
theorem balancedTensorDegreeForget_differential (n : ℕ) :
    (balancedTensorComplex A M N).d (n+1) n ≫ ModuleCat.ofHom (balancedTensorDegreeForget A M N n) =
      ModuleCat.ofHom (balancedTensorDegreeForget A M N (n+1)) ≫
        ModuleCat.ofHom (balancedTensorDifferential A M N) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change p + q = n + 1 at h
  simp only [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    Preadditive.add_comp, Category.assoc, balancedTensorDegreeInclusion_forget_assoc]
  cases p with
  | zero =>
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
    obtain rfl : q = n := by omega
    simp only [ChainComplex.ιTensorObj_D₁_zero_assoc,
      ChainComplex.ιTensorObj_D₂_succ_assoc, zero_add,
      balancedTensorDegreeInclusion_forget, Preadditive.zsmul_comp]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change _ = balancedTensorDifferential A M N (u.val ⊗ₜ[A] v.val)
    rw [balancedTensorDifferential_tmul,
      differential_eq_zero_of_degree_zero M u.property,
      relativeParity_of_mem_degree M u.property]
    simp [coefficientRelativeComplex_d, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      coefficientDegreeInclusionLinear, coefficientDegreeDifferentialLinear,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply, balancedTensorDegreeForget_inclusion]
    change balancedTensorDegreeForget A M N q
      (balancedTensorDegreeInclusion A M N 0 q q (by omega)
        (u ⊗ₜ[A] coefficientDegreeDifferentialLinear A N q v)) = _
    rw [balancedTensorDegreeForget_inclusion]
    rfl
  | succ p =>
    cases q with
    | zero =>
      obtain rfl : p = n := by omega
      simp only [ChainComplex.ιTensorObj_D₂_zero_assoc,
        ChainComplex.ιTensorObj_D₁_succ_assoc, add_zero,
        balancedTensorDegreeInclusion_forget]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      change _ = balancedTensorDifferential A M N (u.val ⊗ₜ[A] v.val)
      rw [balancedTensorDifferential_tmul,
        differential_eq_zero_of_degree_zero N v.property]
      simp [coefficientRelativeComplex_d, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      coefficientDegreeInclusionLinear, coefficientDegreeDifferentialLinear,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply, balancedTensorDegreeForget_inclusion]
      rfl
    | succ q =>
      simp only [ChainComplex.ιTensorObj_D₁_succ_assoc,
        ChainComplex.ιTensorObj_D₂_succ_assoc, balancedTensorDegreeInclusion_forget,
        Preadditive.zsmul_comp]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      change _ = balancedTensorDifferential A M N (u.val ⊗ₜ[A] v.val)
      rw [balancedTensorDifferential_tmul, relativeParity_of_mem_degree M u.property]
      simp [coefficientRelativeComplex_d, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      coefficientDegreeInclusionLinear, coefficientDegreeDifferentialLinear,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
        ModuleCat.MonoidalCategory.whiskerRight_apply, balancedTensorDegreeForget_inclusion,
        TensorProduct.smul_tmul', ← Int.cast_smul_eq_zsmul ℂ]
      change differential M u.val ⊗ₜ[A] v.val +
        ((-1 : ℂ) ^ (p+1)) • balancedTensorDegreeForget A M N n
          (balancedTensorDegreeInclusion A M N (p+1) q n (by omega)
            (u ⊗ₜ[A] coefficientDegreeDifferentialLinear A N q v)) = _
      rw [balancedTensorDegreeForget_inclusion]
      change differential M u.val ⊗ₜ[A] v.val +
        ((-1 : ℂ) ^ (p+1)) • (u.val ⊗ₜ[A] differential N v.val) = _
      rw [TensorProduct.smul_tmul']

end KhanSL2.Factorization

