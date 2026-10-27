module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.Algebra.Exact.Basic

@[expose] public section
noncomputable section
open TensorProduct
namespace KhanSL2.Factorization.TensorCoefficientEquiv

variable {R : Type*} [CommRing R]
variable {S T : Type*} [AddCommGroup S] [Module R S] [AddCommGroup T] [Module R T]
variable {L M N : Type*} [AddCommGroup L] [Module R L]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- Changing the coefficient module intertwines the actual tensor differential. -/
theorem comm (e : S ≃ₗ[R] T) (f : M →ₗ[R] N) :
    (f.lTensor T).comp (e.rTensor M).toLinearMap =
      (e.rTensor N).toLinearMap.comp (f.lTensor S) := by
  change (f.lTensor T).comp (e.toLinearMap.rTensor M) =
    (e.toLinearMap.rTensor N).comp (f.lTensor S)
  rw [LinearMap.lTensor_comp_rTensor,LinearMap.rTensor_comp_lTensor]

theorem surjective (e : S ≃ₗ[R] T) (f : M →ₗ[R] N)
    (h : Function.Surjective (f.lTensor S)) : Function.Surjective (f.lTensor T) := by
  intro y
  obtain ⟨y,rfl⟩ := (e.rTensor N).surjective y
  obtain ⟨x,rfl⟩ := h y
  exact ⟨(e.rTensor M) x,LinearMap.congr_fun (comm e f) x⟩

theorem surjective_iff (e : S ≃ₗ[R] T) (f : M →ₗ[R] N) :
    Function.Surjective (f.lTensor S) ↔ Function.Surjective (f.lTensor T) :=
  ⟨surjective e f,surjective e.symm f⟩

theorem exact_iff (e : S ≃ₗ[R] T) (f : L →ₗ[R] M) (g : M →ₗ[R] N) :
    Function.Exact (f.lTensor S) (g.lTensor S) ↔
      Function.Exact (f.lTensor T) (g.lTensor T) :=
  LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    (f.lTensor S) (g.lTensor S) (f.lTensor T) (g.lTensor T)
    (e.rTensor L).toLinearMap (e.rTensor M).toLinearMap (e.rTensor N).toLinearMap
    (comm e f) (comm e g) (e.rTensor L).surjective (e.rTensor M).bijective (e.rTensor N).injective

end KhanSL2.Factorization.TensorCoefficientEquiv
