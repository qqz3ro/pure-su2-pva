module

public import KhanSL2.Injectivity.TaylorPolynomial
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-!
The final linear-algebra step of sectorwise injectivity.  Ambient duals suffice:
no finite-dimensionality or presentation basis is assumed.
-/

noncomputable section

namespace KhanSL2.SourceDual

open Source

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Realizing every Taylor polynomial by a functional after `f` separates its kernel
on the selected source sector.  The realization hypothesis is explicit. -/
theorem sector_kernel_eq_zero_of_taylor_realization (r s N : ℕ)
    (f : Source →ₗ[ℂ] M)
    (realize : ∀ ell : Source →ₗ[ℂ] ℂ, ∃ targetEll : M →ₗ[ℂ] ℂ,
      taylorPolynomial r s N (targetEll.comp f) = taylorPolynomial r s N ell)
    {a : Source} (ha : a ∈ sector r s N) (hfa : f a = 0) : a = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℂ a).mp
  intro ell
  obtain ⟨targetEll, heq⟩ := realize ell
  have h := eq_on_sector_of_taylorPolynomial_eq (targetEll.comp f) ell heq ha
  rw [LinearMap.comp_apply, hfa, map_zero] at h
  exact h.symm

theorem sector_injOn_of_taylor_realization (r s N : ℕ)
    (f : Source →ₗ[ℂ] M)
    (realize : ∀ ell : Source →ₗ[ℂ] ℂ, ∃ targetEll : M →ₗ[ℂ] ℂ,
      taylorPolynomial r s N (targetEll.comp f) = taylorPolynomial r s N ell) :
    Set.InjOn f (sector r s N) := by
  intro a ha b hb hab
  apply sub_eq_zero.mp
  apply sector_kernel_eq_zero_of_taylor_realization r s N f realize
    ((sector r s N).sub_mem ha hb)
  simp only [map_sub, hab, sub_self]

end KhanSL2.SourceDual
