module

public import KhanSL2.SymmetricFamily.TensorBaseChange
public import KhanSL2.SymmetricFamily.RootPermutation

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The invariants of every labelled-root fibre are exactly its coefficient
scalars. This proves the key invariant line without a regular-representation claim. -/

noncomputable section
open scoped BigOperators TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Conditional

/-- The original coefficient inclusion is injective. -/
theorem rootMap_injective (k : ℕ) : Function.Injective (rootMap k) := by
  intro r s h
  apply (Modules.elementaryAlgEquiv k).injective
  exact Subtype.ext h

/-- The coefficient-linear Reynolds projector on actual root polynomials. -/
def rootAverage (k : ℕ) : Module.End (Depth.RB k) (RootPolynomial k) :=
  permutationNormalization k • ∑ σ : Equiv.Perm (Fin k), (rootPermutationAlgEquiv σ).toLinearMap

private theorem rootPermutation_comp {k : ℕ} (σ τ : Equiv.Perm (Fin k))
    (p : RootPolynomial k) :
    rootPermutationAlgEquiv σ (rootPermutationAlgEquiv τ p) =
      rootPermutationAlgEquiv (σ*τ) p :=
  MvPolynomial.rename_rename τ σ p

/-- The root average is an actual symmetric polynomial. -/
theorem rootAverage_symmetric (k : ℕ) (p : RootPolynomial k) :
    MvPolynomial.IsSymmetric (show MvPolynomial (Fin k) ℂ from rootAverage k p) := by
  intro τ
  change rootPermutationAlgEquiv τ (rootAverage k p) = rootAverage k p
  simp only [rootAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
    map_sum, AlgEquiv.toLinearMap_apply, AlgEquiv.coe_toLinearEquiv, rootPermutation_comp]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => rootPermutationAlgEquiv σ p)

/-- Averaging fixes exactly the original coefficient-polynomial inclusion. -/
theorem rootAverage_rootMap (k : ℕ) (r : Depth.RB k) : rootAverage k (rootMap k r) = rootMap k r := by
  have h (σ : Equiv.Perm (Fin k)) : rootPermutationAlgEquiv σ (rootMap k r) = rootMap k r :=
    (rootPermutationAlgEquiv σ).commutes r
  simp only [rootAverage, LinearMap.smul_apply, LinearMap.sum_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.coe_toLinearEquiv,
    h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul (Depth.RB k), smul_smul, permutationNormalization_card, one_smul]

/-- Read the elementary coefficients of the actual symmetric average. -/
def rootCoefficientProjectionFun (k : ℕ) (p : RootPolynomial k) : Depth.RB k :=
  (Modules.elementaryAlgEquiv k).symm ⟨rootAverage k p,rootAverage_symmetric k p⟩

@[simp] theorem rootMap_coefficientProjection (k : ℕ) (p : RootPolynomial k) :
    rootMap k (rootCoefficientProjectionFun k p) = rootAverage k p := by
  change ((Modules.elementaryAlgEquiv k)
    ((Modules.elementaryAlgEquiv k).symm ⟨rootAverage k p,rootAverage_symmetric k p⟩) :
      MvPolynomial (Fin k) ℂ) = _
  rw [AlgEquiv.apply_symm_apply]

/-- Projection to coefficient scalars, proved linear for the original coefficient map. -/
def rootCoefficientProjection (k : ℕ) : RootPolynomial k →ₗ[Depth.RB k] Depth.RB k where
  toFun := rootCoefficientProjectionFun k
  map_add' p q := by
    apply rootMap_injective k
    rw [map_add, rootMap_coefficientProjection, rootMap_coefficientProjection,
      rootMap_coefficientProjection, map_add]
  map_smul' r p := by
    apply rootMap_injective k
    change rootMap k (rootCoefficientProjectionFun k (r • p)) =
      rootMap k (r * rootCoefficientProjectionFun k p)
    rw [rootMap_coefficientProjection, map_mul, rootMap_coefficientProjection]
    exact (rootAverage k).map_smul r p

/-- Include original coefficient scalars as symmetric root polynomials. -/
def rootCoefficientInclusion (k : ℕ) : Depth.RB k →ₗ[Depth.RB k] RootPolynomial k :=
  Algebra.linearMap (Depth.RB k) (RootPolynomial k)

theorem rootCoefficient_split (k : ℕ) :
    (rootCoefficientProjection k).comp (rootCoefficientInclusion k) = LinearMap.id := by
  apply LinearMap.ext
  intro r
  apply rootMap_injective k
  change rootMap k (rootCoefficientProjectionFun k (rootMap k r)) = rootMap k r
  rw [rootMap_coefficientProjection, rootAverage_rootMap]

theorem rootCoefficient_average (k : ℕ) :
    (rootCoefficientInclusion k).comp (rootCoefficientProjection k) =
      permutationNormalization k • ∑ σ : Equiv.Perm (Fin k), (rootPermutationAlgEquiv σ).toLinearMap := by
  apply LinearMap.ext
  intro p
  exact rootMap_coefficientProjection k p

/-- Base changing the linear root permutation is exactly the already defined algebra permutation. -/
theorem rootPermutation_baseChange (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]
    (σ : Equiv.Perm (Fin k)) :
    (rootPermutationAlgEquiv σ).toLinearMap.baseChange A = (baseRootPermutation k A σ).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a p
  simp only [LinearMap.baseChange_tmul, AlgEquiv.toLinearMap_apply, baseRootPermutation_tmul]

/-- Every actual labelled-root fibre has only the coefficient scalars as symmetric invariants. -/
def rootBaseFixedEquiv (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A] :
    A ≃ₗ[A] fixedOperators (fun σ : Equiv.Perm (Fin k) => (baseRootPermutation k A σ).toLinearMap) := by
  have hi (σ : Equiv.Perm (Fin k)) :
      (rootPermutationAlgEquiv σ).toLinearMap.comp (rootCoefficientInclusion k) =
        rootCoefficientInclusion k := by
    apply LinearMap.ext
    intro r
    exact (rootPermutationAlgEquiv σ).commutes r
  have e := splitAverageBaseChangeEquiv A (rootCoefficientInclusion k)
    (rootCoefficientProjection k) (fun σ : Equiv.Perm (Fin k) => (rootPermutationAlgEquiv σ).toLinearMap)
    (permutationNormalization k) (permutationNormalization_card k)
    (rootCoefficient_split k) (rootCoefficient_average k) hi
  exact (TensorProduct.AlgebraTensorModule.rid (Depth.RB k) A A).symm.trans e

end KhanSL2.SymmetricFamily
