module

public import KhanSL2.Factorization.KunnethTensorModel
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
open KhanSL2.BGG

variable (M N : Type)
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]

/-- Forgetting homogeneous degree intertwines the categorical tensor differential
with the actual signed relative tensor boundary. -/
theorem tensorDegreeForget_differential (n : ℕ) :
    (tensorComplex M N).d (n+1) n ≫ ModuleCat.ofHom (tensorDegreeForget M N n) =
      ModuleCat.ofHom (tensorDegreeForget M N (n+1)) ≫
        ModuleCat.ofHom (relativeTensorDifferential M N) := by
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  change p + q = n + 1 at h
  simp only [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    Preadditive.add_comp, Category.assoc, tensorDegreeInclusion_forget_assoc]
  cases p with
  | zero =>
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show q ≠ 0 by omega)
    obtain rfl : q = n := by omega
    simp only [ChainComplex.ιTensorObj_D₁_zero_assoc,
      ChainComplex.ιTensorObj_D₂_succ_assoc, zero_add,
      tensorDegreeInclusion_forget, Preadditive.zsmul_comp]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change _ = relativeTensorDifferential M N (u.val ⊗ₜ[ℂ] v.val)
    rw [relativeTensorDifferential_tmul,
      differential_eq_zero_of_degree_zero M u.property,
      relativeParity_of_mem_degree M u.property]
    simp [complex_d, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      Submodule.subtype_apply, degreeDifferential_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply, tensorDegreeForget_inclusion]
    change tensorDegreeForget M N q
      (tensorDegreeInclusion M N 0 q q (by omega)
        (u ⊗ₜ[ℂ] degreeDifferential N q v)) = _
    rw [tensorDegreeForget_inclusion]
    rfl
  | succ p =>
    cases q with
    | zero =>
      obtain rfl : p = n := by omega
      simp only [ChainComplex.ιTensorObj_D₂_zero_assoc,
        ChainComplex.ιTensorObj_D₁_succ_assoc, add_zero,
        tensorDegreeInclusion_forget]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      change _ = relativeTensorDifferential M N (u.val ⊗ₜ[ℂ] v.val)
      rw [relativeTensorDifferential_tmul,
        differential_eq_zero_of_degree_zero N v.property]
      simp [complex_d, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      Submodule.subtype_apply, degreeDifferential_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply, tensorDegreeForget_inclusion]
      rfl
    | succ q =>
      simp only [ChainComplex.ιTensorObj_D₁_succ_assoc,
        ChainComplex.ιTensorObj_D₂_succ_assoc, tensorDegreeInclusion_forget,
        Preadditive.zsmul_comp]
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      change _ = relativeTensorDifferential M N (u.val ⊗ₜ[ℂ] v.val)
      rw [relativeTensorDifferential_tmul, relativeParity_of_mem_degree M u.property]
      simp [complex_d, ModuleCat.hom_whiskerLeft, ModuleCat.hom_whiskerRight,
      LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.map_tmul,
      Submodule.subtype_apply, degreeDifferential_apply,
      ModuleCat.MonoidalCategory.whiskerLeft_apply,
        ModuleCat.MonoidalCategory.whiskerRight_apply, tensorDegreeForget_inclusion,
        TensorProduct.smul_tmul', ← Int.cast_smul_eq_zsmul ℂ]
      change differential M u.val ⊗ₜ[ℂ] v.val +
        ((-1 : ℂ) ^ (p+1)) • tensorDegreeForget M N n
          (tensorDegreeInclusion M N (p+1) q n (by omega)
            (u ⊗ₜ[ℂ] degreeDifferential N q v)) = _
      rw [tensorDegreeForget_inclusion]
      change differential M u.val ⊗ₜ[ℂ] v.val +
        ((-1 : ℂ) ^ (p+1)) • (u.val ⊗ₜ[ℂ] differential N v.val) = _
      rw [TensorProduct.smul_tmul']

end KhanSL2.Factorization
