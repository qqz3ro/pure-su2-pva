module

public import KhanSL2.Factorization.CoefficientSplitExactLeft

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization
open BGG

variable {N M P : Type}
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup P] [Module ℂ P] [LieRingModule Current P] [LieModule ℂ Current P]
variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule Current T] [LieModule ℂ Current T]

/-- Constant-equivariant coefficient maps act on the underlying graded tensor
complex, even when they are not themselves chain maps. -/
def tensorCoefficientDegreeMapLeft (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f) (j : ℕ) :
    (tensorComplex T N).X j →ₗ[ℂ] (tensorComplex T M).X j :=
  (tensorDegreeComponent T M j).comp
    ((TensorProduct.map LinearMap.id (coefficientMap f hf)).comp (tensorDegreeForget T N j))

theorem tensorCoefficientDegreeMapLeft_inclusion (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f)
    (p q j : ℕ) (hpq : p+q=j) (u : degree T p) (v : degree N q) :
    tensorCoefficientDegreeMapLeft T f hf j (tensorDegreeInclusion T N p q j hpq (u ⊗ₜ[ℂ] v)) =
      tensorDegreeInclusion T M p q j hpq (u ⊗ₜ[ℂ] coefficientDegreeMap f hf q v) := by
  simp only [tensorCoefficientDegreeMapLeft,LinearMap.comp_apply,tensorDegreeForget_inclusion,
    TensorProduct.map_tmul,Submodule.subtype_apply,LinearMap.id_apply]
  exact tensorDegreeComponent_subtype_tmul T M p q j hpq u (coefficientDegreeMap f hf q v)

theorem tensorCoefficientDegreeMapLeft_forget (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f)
    (j : ℕ) (z : (tensorComplex T N).X j) :
    tensorDegreeForget T M j (tensorCoefficientDegreeMapLeft T f hf j z) =
      TensorProduct.map LinearMap.id (coefficientMap f hf) (tensorDegreeForget T N j z) := by
  have he : ModuleCat.ofHom ((tensorDegreeForget T M j).comp
      (tensorCoefficientDegreeMapLeft T f hf j)) = ModuleCat.ofHom
      ((TensorProduct.map LinearMap.id (coefficientMap f hf)).comp (tensorDegreeForget T N j)) := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change tensorDegreeForget T M j (tensorCoefficientDegreeMapLeft T f hf j
        (tensorDegreeInclusion T N p q j hpq (u ⊗ₜ[ℂ] v))) =
      TensorProduct.map LinearMap.id (coefficientMap f hf)
        (tensorDegreeForget T N j (tensorDegreeInclusion T N p q j hpq (u ⊗ₜ[ℂ] v)))
    rw [tensorCoefficientDegreeMapLeft_inclusion,tensorDegreeForget_inclusion,
      tensorDegreeForget_inclusion]
    rfl
  exact congrArg (fun q => q.hom z) he

@[simp] theorem tensorCoefficientDegreeMapLeft_id (j : ℕ) :
    tensorCoefficientDegreeMapLeft T (LinearMap.id : N →ₗ[ℂ] N) ConstantEquivariant.id j =
      LinearMap.id := by
  ext z
  apply tensorDegreeForget_injective T N j
  simp only [tensorCoefficientDegreeMapLeft_forget,coefficientMap_id,TensorProduct.map_id,
    LinearMap.id_apply]

theorem tensorCoefficientDegreeMapLeft_comp (f : N →ₗ[ℂ] M) (g : M →ₗ[ℂ] P)
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g) (j : ℕ) :
    tensorCoefficientDegreeMapLeft T (g.comp f) (hg.comp hf) j =
      (tensorCoefficientDegreeMapLeft T g hg j).comp (tensorCoefficientDegreeMapLeft T f hf j) := by
  ext z
  apply tensorDegreeForget_injective T P j
  simp only [LinearMap.comp_apply,tensorCoefficientDegreeMapLeft_forget,coefficientMap_comp]
  rw [coefficientMap_comp f g hf hg]
  have h := TensorProduct.map_comp (LinearMap.id : RelativeChains T →ₗ[ℂ] _) (coefficientMap g hg)
    LinearMap.id (coefficientMap f hf)
  simpa only [LinearMap.id_comp,LinearMap.comp_apply] using
    LinearMap.congr_fun h (tensorDegreeForget T N j z)

theorem tensorCoefficientDegreeMapLeft_add (f g : N →ₗ[ℂ] M)
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g) (j : ℕ) :
    tensorCoefficientDegreeMapLeft T (f+g) (hf.add hg) j =
      tensorCoefficientDegreeMapLeft T f hf j + tensorCoefficientDegreeMapLeft T g hg j := by
  ext z
  apply tensorDegreeForget_injective T M j
  simp only [LinearMap.add_apply,map_add,tensorCoefficientDegreeMapLeft_forget,
    coefficientMap_add,TensorProduct.map_add_right]
  rw [coefficientMap_add f g hf hg]
  simp only [TensorProduct.map_add_left,TensorProduct.map_add_right,LinearMap.add_apply]

@[simp] theorem tensorCoefficientDegreeMapLeft_zero (j : ℕ) :
    tensorCoefficientDegreeMapLeft T (0 : N →ₗ[ℂ] M) ConstantEquivariant.zero j = 0 := by
  ext z
  apply tensorDegreeForget_injective T M j
  simp only [tensorCoefficientDegreeMapLeft_forget,coefficientMap_zero,TensorProduct.map_zero_right,
    LinearMap.zero_apply,map_zero]

/-- For current-equivariant maps this graded construction is exactly the
component of the canonical categorical tensor map. -/
theorem tensorCoefficientDegreeMapLeft_lie (f : N →ₗ⁅ℂ,Current⁆ M) (j : ℕ) :
    tensorCoefficientDegreeMapLeft T f.toLinearMap (constantEquivariant_of_lieHom f) j =
      ((HomologicalComplex.tensorHom (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T))
        (complexMap f)).f j).hom := by
  ext z
  apply tensorDegreeForget_injective T M j
  rw [tensorCoefficientDegreeMapLeft_forget]
  have h := congrArg (fun q => q.hom z)
    (tensorDegreeForget_tensorHom (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) f j)
  have hid : coefficientMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T).toLinearMap
      (constantEquivariant_of_lieHom LieModuleHom.id) = LinearMap.id := coefficientMap_id
  rw [hid] at h
  simpa only [ModuleCat.hom_comp,ModuleCat.hom_ofHom,LinearMap.comp_apply] using h.symm

end KhanSL2.Factorization