module

public import KhanSL2.Factorization.CoefficientSplitExact

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
def tensorCoefficientDegreeMap (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f) (j : ℕ) :
    (tensorComplex N T).X j →ₗ[ℂ] (tensorComplex M T).X j :=
  (tensorDegreeComponent M T j).comp
    ((TensorProduct.map (coefficientMap f hf) LinearMap.id).comp (tensorDegreeForget N T j))

theorem tensorCoefficientDegreeMap_inclusion (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f)
    (p q j : ℕ) (hpq : p+q=j) (u : degree N p) (v : degree T q) :
    tensorCoefficientDegreeMap T f hf j (tensorDegreeInclusion N T p q j hpq (u ⊗ₜ[ℂ] v)) =
      tensorDegreeInclusion M T p q j hpq (coefficientDegreeMap f hf p u ⊗ₜ[ℂ] v) := by
  simp only [tensorCoefficientDegreeMap,LinearMap.comp_apply,tensorDegreeForget_inclusion,
    TensorProduct.map_tmul,Submodule.subtype_apply,LinearMap.id_apply]
  exact tensorDegreeComponent_subtype_tmul M T p q j hpq (coefficientDegreeMap f hf p u) v

theorem tensorCoefficientDegreeMap_forget (f : N →ₗ[ℂ] M) (hf : ConstantEquivariant f)
    (j : ℕ) (z : (tensorComplex N T).X j) :
    tensorDegreeForget M T j (tensorCoefficientDegreeMap T f hf j z) =
      TensorProduct.map (coefficientMap f hf) LinearMap.id (tensorDegreeForget N T j z) := by
  have he : ModuleCat.ofHom ((tensorDegreeForget M T j).comp
      (tensorCoefficientDegreeMap T f hf j)) = ModuleCat.ofHom
      ((TensorProduct.map (coefficientMap f hf) LinearMap.id).comp (tensorDegreeForget N T j)) := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change tensorDegreeForget M T j (tensorCoefficientDegreeMap T f hf j
        (tensorDegreeInclusion N T p q j hpq (u ⊗ₜ[ℂ] v))) =
      TensorProduct.map (coefficientMap f hf) LinearMap.id
        (tensorDegreeForget N T j (tensorDegreeInclusion N T p q j hpq (u ⊗ₜ[ℂ] v)))
    rw [tensorCoefficientDegreeMap_inclusion,tensorDegreeForget_inclusion,
      tensorDegreeForget_inclusion]
    rfl
  exact congrArg (fun q => q.hom z) he

@[simp] theorem tensorCoefficientDegreeMap_id (j : ℕ) :
    tensorCoefficientDegreeMap T (LinearMap.id : N →ₗ[ℂ] N) ConstantEquivariant.id j =
      LinearMap.id := by
  ext z
  apply tensorDegreeForget_injective N T j
  simp only [tensorCoefficientDegreeMap_forget,coefficientMap_id,TensorProduct.map_id,
    LinearMap.id_apply]

theorem tensorCoefficientDegreeMap_comp (f : N →ₗ[ℂ] M) (g : M →ₗ[ℂ] P)
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g) (j : ℕ) :
    tensorCoefficientDegreeMap T (g.comp f) (hg.comp hf) j =
      (tensorCoefficientDegreeMap T g hg j).comp (tensorCoefficientDegreeMap T f hf j) := by
  ext z
  apply tensorDegreeForget_injective P T j
  simp only [LinearMap.comp_apply,tensorCoefficientDegreeMap_forget,coefficientMap_comp]
  rw [coefficientMap_comp f g hf hg]
  have h := TensorProduct.map_comp (coefficientMap g hg) (LinearMap.id : RelativeChains T →ₗ[ℂ] _)
    (coefficientMap f hf) LinearMap.id
  simpa only [LinearMap.id_comp,LinearMap.comp_apply] using
    LinearMap.congr_fun h (tensorDegreeForget N T j z)

theorem tensorCoefficientDegreeMap_add (f g : N →ₗ[ℂ] M)
    (hf : ConstantEquivariant f) (hg : ConstantEquivariant g) (j : ℕ) :
    tensorCoefficientDegreeMap T (f+g) (hf.add hg) j =
      tensorCoefficientDegreeMap T f hf j + tensorCoefficientDegreeMap T g hg j := by
  ext z
  apply tensorDegreeForget_injective M T j
  simp only [LinearMap.add_apply,map_add,tensorCoefficientDegreeMap_forget,
    coefficientMap_add,TensorProduct.map_add_left]
  rw [coefficientMap_add f g hf hg]
  simp only [TensorProduct.map_add_left,TensorProduct.map_add_right,LinearMap.add_apply]

@[simp] theorem tensorCoefficientDegreeMap_zero (j : ℕ) :
    tensorCoefficientDegreeMap T (0 : N →ₗ[ℂ] M) ConstantEquivariant.zero j = 0 := by
  ext z
  apply tensorDegreeForget_injective M T j
  simp only [tensorCoefficientDegreeMap_forget,coefficientMap_zero,TensorProduct.map_zero_left,
    LinearMap.zero_apply,map_zero]

/-- For current-equivariant maps this graded construction is exactly the
component of the canonical categorical tensor map. -/
theorem tensorCoefficientDegreeMap_lie (f : N →ₗ⁅ℂ,Current⁆ M) (j : ℕ) :
    tensorCoefficientDegreeMap T f.toLinearMap (constantEquivariant_of_lieHom f) j =
      ((HomologicalComplex.tensorHom (complexMap f)
        (complexMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T))).f j).hom := by
  ext z
  apply tensorDegreeForget_injective M T j
  rw [tensorCoefficientDegreeMap_forget]
  have h := congrArg (fun q => q.hom z)
    (tensorDegreeForget_tensorHom f (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T) j)
  have hid : coefficientMap (LieModuleHom.id : T →ₗ⁅ℂ,Current⁆ T).toLinearMap
      (constantEquivariant_of_lieHom LieModuleHom.id) = LinearMap.id := coefficientMap_id
  rw [hid] at h
  simpa only [ModuleCat.hom_comp,ModuleCat.hom_ofHom,LinearMap.comp_apply] using h.symm

end KhanSL2.Factorization