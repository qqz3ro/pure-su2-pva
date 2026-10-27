module

public import KhanSL2.PolynomialBGG.ProjectiveModelDeriv
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The coefficient-degree projector on the actual exterior algebra commutes
with all induced derivations. This makes the degree restriction compatible
with both the coefficient ring and the diagonal constant Lie action. -/

noncomputable section
namespace KhanSL2.PolynomialBGG

variable (M : Type*) [AddCommGroup M] [Module ℂ M]

/-- The canonical degree-B component of the exterior algebra. -/
def exteriorProjection (B : ℕ) : ExteriorAlgebra ℂ M →ₗ[ℂ] ⋀[ℂ]^B M :=
  (DirectSum.component ℂ ℕ (fun n => ⋀[ℂ]^n M) B).comp
    (DirectSum.decomposeLinearEquiv (fun n : ℕ => ⋀[ℂ]^n M)).toLinearMap

@[simp] theorem exteriorProjection_coe (B : ℕ) (u : ⋀[ℂ]^B M) :
    exteriorProjection M B u = u := by
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_same (fun n : ℕ => ⋀[ℂ]^n M) u.property

theorem exteriorProjection_of_mem_ne (B n : ℕ) (hne : n ≠ B)
    (u : ExteriorAlgebra ℂ M) (hu : u ∈ ⋀[ℂ]^n M) : exteriorProjection M B u = 0 := by
  apply Subtype.ext
  exact DirectSum.decompose_of_mem_ne (fun n : ℕ => ⋀[ℂ]^n M) hu hne

/-- The degree projection intertwines every induced exterior derivation. -/
theorem exteriorProjection_derivExt (B : ℕ) (D : Module.End ℂ M)
    (u : ExteriorAlgebra ℂ M) :
    exteriorProjection M B (LieChains.derivExt D u) =
      exteriorDeriv B D (exteriorProjection M B u) := by
  induction u using DirectSum.Decomposition.inductionOn (fun n : ℕ => ⋀[ℂ]^n M) with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | @homogeneous n u =>
    by_cases h : n = B
    · subst n
      have hD : LieChains.derivExt D (u : ExteriorAlgebra ℂ M) ∈ ⋀[ℂ]^B M :=
        LieChains.derivExt_mem_exteriorPower D u.property
      rw [show LieChains.derivExt D (u : ExteriorAlgebra ℂ M) =
          (⟨LieChains.derivExt D u, hD⟩ : ⋀[ℂ]^B M) from rfl,
        exteriorProjection_coe, exteriorProjection_coe]
      rfl
    · rw [exteriorProjection_of_mem_ne M B n h _
          (LieChains.derivExt_mem_exteriorPower D u.property),
        exteriorProjection_of_mem_ne M B n h _ u.property, map_zero]

/-- The actual exterior-degree projection is a left inverse to inclusion. -/
theorem exteriorProjection_comp_subtype (B : ℕ) :
    (exteriorProjection M B).comp (⋀[ℂ]^B M).subtype = LinearMap.id := by
  apply LinearMap.ext
  intro x
  exact exteriorProjection_coe M B x

end KhanSL2.PolynomialBGG
