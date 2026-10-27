module

public import KhanSL2.SymmetricFamily.LabelledRoots

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The honest permutation representation on finite color tensors. Its action
is inverse to slot precomposition, matching direct root renaming in quotient
assignment transports. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

/-- Relabel color words by the inverse slot permutation. -/
def colorWordPermutation {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (Fin k → Fin 3) ≃ (Fin k → Fin 3) where
  toFun c := c ∘ σ.symm
  invFun c := c ∘ σ
  left_inv c := by funext i; simp
  right_inv c := by funext i; simp

/-- The genuine color permutation equivalence. -/
def colorPermutationEquiv {k : ℕ} (σ : Equiv.Perm (Fin k)) : Color k ≃ₗ[ℂ] Color k :=
  (Pi.basisFun ℂ (Fin k → Fin 3)).equiv
    (Pi.basisFun ℂ (Fin k → Fin 3)) (colorWordPermutation σ)

@[simp] theorem colorPermutationEquiv_basis {k : ℕ} (σ : Equiv.Perm (Fin k))
    (c : Fin k → Fin 3) :
    colorPermutationEquiv σ (Pi.basisFun ℂ (Fin k → Fin 3) c) =
      Pi.basisFun ℂ (Fin k → Fin 3) (c ∘ σ.symm) :=
  Module.Basis.equiv_apply _ c _ _

/-- This honest action is precisely the previously specified inverse slot map. -/
theorem colorPermutationEquiv_toLinearMap {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (colorPermutationEquiv σ).toLinearMap = colorPermute σ.symm := by
  apply (Pi.basisFun ℂ (Fin k → Fin 3)).ext
  intro c
  rw [colorPermute_basis]
  exact colorPermutationEquiv_basis σ c

/-- Bundle the actual color permutations as a group representation. -/
def colorPermutationRepresentation (k : ℕ) : Equiv.Perm (Fin k) →* (Color k ≃ₗ[ℂ] Color k) where
  toFun := colorPermutationEquiv
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun ℂ (Fin k → Fin 3)).ext
    intro c
    simp only [LinearEquiv.coe_coe, colorPermutationEquiv_basis]
    rfl
  map_mul' σ τ := by
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun ℂ (Fin k → Fin 3)).ext
    intro c
    change colorPermutationEquiv (σ*τ) (Pi.basisFun ℂ (Fin k → Fin 3) c) =
      colorPermutationEquiv σ (colorPermutationEquiv τ (Pi.basisFun ℂ (Fin k → Fin 3) c))
    rw [colorPermutationEquiv_basis, colorPermutationEquiv_basis, colorPermutationEquiv_basis]
    rfl

end KhanSL2.SymmetricFamily
