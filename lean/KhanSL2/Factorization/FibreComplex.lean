module

public import KhanSL2.Factorization.FibreKernel

@[expose] public section
noncomputable section
open TensorProduct
namespace KhanSL2.Factorization.FibreExactness

variable {R : Type*} [CommRing R]
variable (C : ℕ → Type*) [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]
variable [∀ n, Module.Finite R (C n)] [∀ n, Module.Projective R (C n)]
variable (d : ∀ n, C (n+1) →ₗ[R] C n)
variable (hsq : ∀ n, (d n).comp (d (n+1)) = 0)
include hsq

/-- The successive images become projective by induction from homological
index zero. This proves the splitting needed to lift fibre exactness. -/
theorem range_projective_of_maximal_fibres
    (h₀ : ∀ (p : Ideal R) [p.IsMaximal], Function.Surjective ((d 0).lTensor p.ResidueField))
    (h : ∀ n (p : Ideal R) [p.IsMaximal],
      Function.Exact ((d (n+1)).lTensor p.ResidueField) ((d n).lTensor p.ResidueField))
    (n : ℕ) : Module.Projective R (LinearMap.range (d n)) := by
  induction n with
  | zero =>
    have hsurj := surjective_of_maximal_fibres (d 0) h₀
    let e : LinearMap.range (d 0) ≃ₗ[R] C 0 :=
      LinearEquiv.ofBijective (LinearMap.range (d 0)).subtype
        ⟨Subtype.val_injective,fun y => ⟨⟨y,hsurj y⟩,rfl⟩⟩
    exact Module.Projective.of_equiv e.symm
  | succ n ih =>
    let := ih
    have he := exact_of_maximal_fibres_of_projective_range (d n) (d (n+1)) (hsq n) (h n)
    let := kernel_projective_of_projective_range (d n)
    exact Module.Projective.of_equiv (LinearEquiv.ofEq _ _ (LinearMap.exact_iff.mp he))

/-- A nonnegative complex of finite projective modules is acyclic if its
complexes of maximal residue fibres are acyclic. No ordinary homology/base-change
identity is assumed. In particular this applies to bounded finite BGG complexes. -/
theorem exact_of_maximal_fibres
    (h₀ : ∀ (p : Ideal R) [p.IsMaximal], Function.Surjective ((d 0).lTensor p.ResidueField))
    (h : ∀ n (p : Ideal R) [p.IsMaximal],
      Function.Exact ((d (n+1)).lTensor p.ResidueField) ((d n).lTensor p.ResidueField)) :
    Function.Surjective (d 0) ∧ ∀ n, Function.Exact (d (n+1)) (d n) := by
  refine ⟨surjective_of_maximal_fibres (d 0) h₀,fun n => ?_⟩
  let := range_projective_of_maximal_fibres C d hsq h₀ h n
  exact exact_of_maximal_fibres_of_projective_range (d n) (d (n+1)) (hsq n) (h n)

end KhanSL2.Factorization.FibreExactness
