module

public import KhanSL2.Factorization.CoefficientMapsExact
public import KhanSL2.Factorization.ShuffleComplexNaturality

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG

variable {N M P : Type}
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]

/-- A current-module short exact sequence with a specified splitting only for
the constant action. No positive-current equivariance of the splitting is assumed. -/
structure ConstantSplitExact (i : N →ₗ⁅ℂ,Current⁆ M) (p : M →ₗ⁅ℂ,Current⁆ P) where
  retraction : M →ₗ[ℂ] N
  sectionMap : P →ₗ[ℂ] M
  retraction_constant : ConstantEquivariant retraction
  section_constant : ConstantEquivariant sectionMap
  zero_comp : p.toLinearMap.comp i.toLinearMap = 0
  left_inverse : retraction.comp i.toLinearMap = LinearMap.id
  right_inverse : p.toLinearMap.comp sectionMap = LinearMap.id
  decomposition : i.toLinearMap.comp retraction + sectionMap.comp p.toLinearMap = LinearMap.id

namespace ConstantSplitExact
variable {i : N →ₗ⁅ℂ,Current⁆ M} {p : M →ₗ⁅ℂ,Current⁆ P}

/-- Exactness is for the actual coefficient-induced maps in every CE degree. -/
theorem chain_shortExact (h : ConstantSplitExact i p) (j : ℕ) :
    Function.Injective ((complexMap i).f j) ∧
      Function.Exact ((complexMap i).f j) ((complexMap p).f j) ∧
      Function.Surjective ((complexMap p).f j) := by
  obtain ⟨hi,he,hp⟩ := coefficientDegreeMap_shortExact_of_split
    i.toLinearMap p.toLinearMap h.retraction h.sectionMap
    (constantEquivariant_of_lieHom i) (constantEquivariant_of_lieHom p)
    h.retraction_constant h.section_constant h.zero_comp h.left_inverse
    h.right_inverse h.decomposition j
  refine ⟨hi,?_,hp⟩
  exact LinearMap.exact_iff.mpr he.symm

variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule Current T] [LieModule ℂ Current T]

/-- Tensoring coefficients retains the same constant splitting. -/
def tensorRight (h : ConstantSplitExact i p) :
    ConstantSplitExact
      (TensorProduct.LieModule.map i (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T))
      (TensorProduct.LieModule.map p (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T)) where
  retraction := TensorProduct.map h.retraction LinearMap.id
  sectionMap := TensorProduct.map h.sectionMap LinearMap.id
  retraction_constant := h.retraction_constant.tensorMap ConstantEquivariant.id
  section_constant := h.section_constant.tensorMap ConstantEquivariant.id
  zero_comp := by
    ext m t
    change p (i m) ⊗ₜ[ℂ] t = 0
    have hz := LinearMap.congr_fun h.zero_comp m
    change p (i m) = 0 at hz
    rw [hz,TensorProduct.zero_tmul]
  left_inverse := by
    ext m t
    change h.retraction (i m) ⊗ₜ[ℂ] t = m ⊗ₜ[ℂ] t
    exact congrArg (fun z => z ⊗ₜ[ℂ] t) (LinearMap.congr_fun h.left_inverse m)
  right_inverse := by
    ext m t
    change p (h.sectionMap m) ⊗ₜ[ℂ] t = m ⊗ₜ[ℂ] t
    exact congrArg (fun z => z ⊗ₜ[ℂ] t) (LinearMap.congr_fun h.right_inverse m)
  decomposition := by
    ext m t
    change i (h.retraction m) ⊗ₜ[ℂ] t + h.sectionMap (p m) ⊗ₜ[ℂ] t = m ⊗ₜ[ℂ] t
    rw [← TensorProduct.add_tmul]
    exact congrArg (fun z => z ⊗ₜ[ℂ] t) (LinearMap.congr_fun h.decomposition m)

end ConstantSplitExact
end KhanSL2.Factorization