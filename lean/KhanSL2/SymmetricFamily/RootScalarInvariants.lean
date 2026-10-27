module

public import KhanSL2.SymmetricFamily.RootAveraging

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Explicit scalar identification of symmetric vectors in every actual root
fibre, retaining the original inclusion and coefficient projection. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]

/-- Base change of the original coefficient inclusion is the actual scalar map. -/
theorem rootCoefficientInclusion_baseChange (x : A ⊗[Depth.RB k] Depth.RB k) :
    (rootCoefficientInclusion k).baseChange A x =
      algebraMap A (RootBase k A)
        (TensorProduct.AlgebraTensorModule.rid (Depth.RB k) A A x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a r =>
    change a ⊗ₜ[Depth.RB k] rootMap k r = (r • a) ⊗ₜ[Depth.RB k] (1 : RootPolynomial k)
    rw [TensorProduct.smul_tmul]
    congr 1
    change rootMap k r = rootMap k r * 1
    exact (mul_one _).symm

/-- Every simultaneous root-permutation invariant is an actual coefficient scalar. -/
theorem rootBase_fixed_isScalar (x : RootBase k A)
    (hx : ∀ σ : Equiv.Perm (Fin k), baseRootPermutation k A σ x = x) :
    ∃ a : A, algebraMap A (RootBase k A) a = x := by
  have h := LinearMap.congr_fun
    (splitAverage_baseChange A (rootCoefficientInclusion k) (rootCoefficientProjection k)
      (fun σ : Equiv.Perm (Fin k) => (rootPermutationAlgEquiv σ).toLinearMap)
      (permutationNormalization k) (rootCoefficient_average k)) x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    rootPermutation_baseChange, AlgEquiv.toLinearMap_apply, hx,
    Finset.sum_const, Finset.card_univ] at h
  rw [← Nat.cast_smul_eq_nsmul (Depth.RB k), smul_smul,
    permutationNormalization_card, one_smul] at h
  refine ⟨TensorProduct.AlgebraTensorModule.rid (Depth.RB k) A A
    ((rootCoefficientProjection k).baseChange A x),?_⟩
  rw [← rootCoefficientInclusion_baseChange]
  exact h

end KhanSL2.SymmetricFamily
