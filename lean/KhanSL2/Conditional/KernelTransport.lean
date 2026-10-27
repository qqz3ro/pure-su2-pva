module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.RingTheory.Support

@[expose] public section

/-! Kernel and support transport through an actual linear equivalence. -/

namespace KhanSL2.Conditional

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- Restrict the given equivalence to the kernels of the comparison and its pullback. -/
def kerCompEquiv (e : M ≃ₗ[R] N) (f : N →ₗ[R] P) :
    LinearMap.ker (f.comp e.toLinearMap) ≃ₗ[R] LinearMap.ker f :=
  e.ofSubmodule' (LinearMap.ker f)

@[simp] theorem kerCompEquiv_apply (e : M ≃ₗ[R] N) (f : N →ₗ[R] P)
    (x : LinearMap.ker (f.comp e.toLinearMap)) :
    (kerCompEquiv e f x : N) = e (x : M) :=
  e.ofSubmodule'_apply (LinearMap.ker f) x

@[simp] theorem kerCompEquiv_symm_apply (e : M ≃ₗ[R] N) (f : N →ₗ[R] P)
    (x : LinearMap.ker f) :
    ((kerCompEquiv e f).symm x : M) = e.symm (x : N) :=
  e.ofSubmodule'_symm_apply (LinearMap.ker f) x

/-- Pulling a comparison back through a linear equivalence preserves its kernel support. -/
theorem support_ker_comp_equiv (e : M ≃ₗ[R] N) (f : N →ₗ[R] P) :
    Module.support R (LinearMap.ker (f.comp e.toLinearMap)) =
      Module.support R (LinearMap.ker f) :=
  (kerCompEquiv e f).support_eq

/-- A support condition transports in either direction without finite-generation assumptions. -/
theorem support_ker_comp_subset_iff (e : M ≃ₗ[R] N) (f : N →ₗ[R] P)
    (Z : Set (PrimeSpectrum R)) :
    Module.support R (LinearMap.ker (f.comp e.toLinearMap)) ⊆ Z ↔
      Module.support R (LinearMap.ker f) ⊆ Z := by
  rw [support_ker_comp_equiv]

/-- Injectivity of a comparison is unchanged by identifying its domain linearly. -/
theorem injective_comp_equiv_iff (e : M ≃ₗ[R] N) (f : N →ₗ[R] P) :
    Function.Injective (f.comp e.toLinearMap) ↔ Function.Injective f :=
  e.toEquiv.injective_comp f

end KhanSL2.Conditional
