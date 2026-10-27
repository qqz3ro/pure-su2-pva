module

public import TauCeti.LinearAlgebra.End.LocallyNilpotent
public import Mathlib.Algebra.Module.Submodule.Lattice

@[expose] public section
namespace KhanSL2.BGG

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]

/-- Strict lowering of an increasing filtration gives an explicit nilpotence bound
on each filtered piece. No uniform bound or completion is assumed. -/
theorem pow_eq_zero_of_filtration (F : ℕ → Submodule R M) (h0 : F 0=⊥)
    (f : Module.End R M) (hf : ∀ n x, x ∈ F (n+1) → f x ∈ F n)
    (n : ℕ) {x : M} (hx : x ∈ F n) : (f^n) x=0 := by
  induction n generalizing x with
  | zero =>
    have hz : x=0 := by simpa only [h0, Submodule.mem_bot] using hx
    rw [hz, map_zero]
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (hf n x hx)

/-- Exhaustivity converts the piecewise bound into pointwise local nilpotence. -/
theorem locallyNilpotent_of_filtration (F : ℕ → Submodule R M) (h0 : F 0=⊥)
    (hcover : ∀ x, ∃ n, x ∈ F n) (f : Module.End R M)
    (hf : ∀ n x, x ∈ F (n+1) → f x ∈ F n) : ∀ x, ∃ n, (f^n) x=0 := by
  intro x
  obtain ⟨n,hn⟩ := hcover x
  exact ⟨n,pow_eq_zero_of_filtration F h0 f hf n hn⟩

/-- The finite perturbation inverse exists under a proved lowering/exhaustivity bound. -/
theorem isUnit_one_add_of_filtration (F : ℕ → Submodule R M) (h0 : F 0=⊥)
    (hcover : ∀ x, ∃ n, x ∈ F n) (f : Module.End R M)
    (hf : ∀ n x, x ∈ F (n+1) → f x ∈ F n) : IsUnit (1+f) :=
  Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero f
    (locallyNilpotent_of_filtration F h0 hcover f hf)

end KhanSL2.BGG