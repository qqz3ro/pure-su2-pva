module
public import KhanSL2.Factorization.CoefficientSplitExact
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace KhanSL2.Factorization.ConstantSplitExact
open KhanSL2.BGG
variable {N M P : Type}
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]
variable {i : N →ₗ⁅ℂ,Current⁆ M} {p : M →ₗ⁅ℂ,Current⁆ P}
variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule Current T] [LieModule ℂ Current T]

/-- The analogous constant splitting when coefficients vary in the second factor. -/
def tensorLeft (h : ConstantSplitExact i p) :
    ConstantSplitExact
      (TensorProduct.LieModule.map (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) i)
      (TensorProduct.LieModule.map (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) p) where
  retraction := TensorProduct.map LinearMap.id h.retraction
  sectionMap := TensorProduct.map LinearMap.id h.sectionMap
  retraction_constant := ConstantEquivariant.id.tensorMap h.retraction_constant
  section_constant := ConstantEquivariant.id.tensorMap h.section_constant
  zero_comp := by
    ext t m
    change t ⊗ₜ[ℂ] p (i m) = 0
    have hz := LinearMap.congr_fun h.zero_comp m
    change p (i m) = 0 at hz
    rw [hz,TensorProduct.tmul_zero]
  left_inverse := by
    ext t m
    change t ⊗ₜ[ℂ] h.retraction (i m) = t ⊗ₜ[ℂ] m
    exact congrArg (fun z => t ⊗ₜ[ℂ] z) (LinearMap.congr_fun h.left_inverse m)
  right_inverse := by
    ext t m
    change t ⊗ₜ[ℂ] p (h.sectionMap m) = t ⊗ₜ[ℂ] m
    exact congrArg (fun z => t ⊗ₜ[ℂ] z) (LinearMap.congr_fun h.right_inverse m)
  decomposition := by
    ext t m
    change t ⊗ₜ[ℂ] i (h.retraction m) + t ⊗ₜ[ℂ] h.sectionMap (p m) = t ⊗ₜ[ℂ] m
    rw [← TensorProduct.tmul_add]
    exact congrArg (fun z => t ⊗ₜ[ℂ] z) (LinearMap.congr_fun h.decomposition m)
end KhanSL2.Factorization.ConstantSplitExact