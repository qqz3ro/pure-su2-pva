module

public import KhanSL2.Factorization.ShuffleDevissage
public import KhanSL2.Factorization.ShuffleDevissageSecond

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG
variable {N M : Type}
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]

/-- A current-equivariant coefficient retraction gives the exact chain retraction. -/
theorem complexMap_retraction (i : N →ₗ⁅ℂ,Current⁆ M) (r : M →ₗ⁅ℂ,Current⁆ N)
    (h : r.toLinearMap.comp i.toLinearMap = LinearMap.id) :
    complexMap i ≫ complexMap r = 𝟙 (complex N) := by
  ext j : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact coefficientDegreeMap_leftInverse i.toLinearMap r.toLinearMap
    (constantEquivariant_of_lieHom i) (constantEquivariant_of_lieHom r) h j z

variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule Current T] [LieModule ℂ Current T]

/-- The specified shuffle passes to current-module retracts in its first factor. -/
theorem shuffle_quasiIso_of_retract_first (i : N →ₗ⁅ℂ,Current⁆ M) (r : M →ₗ⁅ℂ,Current⁆ N)
    (h : r.toLinearMap.comp i.toLinearMap = LinearMap.id)
    [QuasiIso (shuffleComplex M T)] : QuasiIso (shuffleComplex N T) := by
  apply NonnegativeCone.quasiIso_of_retract_square
    (complexMap (TensorProduct.LieModule.map i (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (complexMap (TensorProduct.LieModule.map r (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (HomologicalComplex.tensorHom (complexMap i) (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (HomologicalComplex.tensorHom (complexMap r) (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)))
    (shuffleComplex N T) (shuffleComplex M T)
    (shuffleComplex_natural i (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)).symm
    (shuffleComplex_natural r (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)).symm
  · apply complexMap_retraction
    ext m t
    change r (i m) ⊗ₜ[ℂ] t = m ⊗ₜ[ℂ] t
    exact congrArg (fun z => z ⊗ₜ[ℂ] t) (LinearMap.congr_fun h m)
  · ext j : 1
    apply ModuleCat.hom_ext
    simp only [HomologicalComplex.comp_f,HomologicalComplex.id_f,ModuleCat.hom_comp,ModuleCat.hom_id]
    rw [← tensorCoefficientDegreeMap_lie,← tensorCoefficientDegreeMap_lie,
      ← tensorCoefficientDegreeMap_comp]
    simp only [h,tensorCoefficientDegreeMap_id]

/-- The same direct-summand statement in the second factor, without assuming a
shuffle symmetry or changing the specified map. -/
theorem shuffle_quasiIso_of_retract_second (i : N →ₗ⁅ℂ,Current⁆ M) (r : M →ₗ⁅ℂ,Current⁆ N)
    (h : r.toLinearMap.comp i.toLinearMap = LinearMap.id)
    [QuasiIso (shuffleComplex T M)] : QuasiIso (shuffleComplex T N) := by
  apply NonnegativeCone.quasiIso_of_retract_square
    (complexMap (TensorProduct.LieModule.map (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) i))
    (complexMap (TensorProduct.LieModule.map (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) r))
    (HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap i))
    (HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) (complexMap r))
    (shuffleComplex T N) (shuffleComplex T M)
    (shuffleComplex_natural (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) i).symm
    (shuffleComplex_natural (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) r).symm
  · apply complexMap_retraction
    ext t m
    change t ⊗ₜ[ℂ] r (i m) = t ⊗ₜ[ℂ] m
    exact congrArg (fun z => t ⊗ₜ[ℂ] z) (LinearMap.congr_fun h m)
  · ext j : 1
    apply ModuleCat.hom_ext
    simp only [HomologicalComplex.comp_f,HomologicalComplex.id_f,ModuleCat.hom_comp,ModuleCat.hom_id]
    rw [← tensorCoefficientDegreeMapLeft_lie,← tensorCoefficientDegreeMapLeft_lie,
      ← tensorCoefficientDegreeMapLeft_comp]
    simp only [h,tensorCoefficientDegreeMapLeft_id]

end KhanSL2.Factorization