module

public import KhanSL2.SymmetricFamily.RootCharacteristic
public import KhanSL2.Factorization.WeightedRootsAlgebra

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Actual labelled-root rings over coefficient charts and their coprime splitting.
The splitting remains valid for nonreduced coefficient rings. -/

noncomputable section
open Polynomial
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization.WeightedRoots

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]

/-- The actual base change of the labelled-root ring through its fixed coefficient map. -/
abbrev RootBase := A ⊗[Depth.RB k] RootPolynomial k

/-- Include the labelled-root ring into its base change. -/
def rootBaseRight : RootPolynomial k →ₐ[Depth.RB k] RootBase k A :=
  Algebra.TensorProduct.includeRight

/-- The labelled roots after the actual coefficient base change. -/
def baseRoot (i : Fin k) : RootBase k A :=
  rootBaseRight k A (show RootPolynomial k from MvPolynomial.X i)

/-- The original universal polynomial splits into these actual labelled roots. -/
theorem univPoly_map_baseRoot :
    (Collision.univPoly k).map (algebraMap (Depth.RB k) (RootBase k A)) =
      ∏ i : Fin k, (Polynomial.X - Polynomial.C (baseRoot k A i)) := by
  have h := congrArg (Polynomial.map (rootBaseRight k A).toRingHom) (univPoly_map_rootMap k)
  have hc : (rootBaseRight k A).toRingHom.comp (rootMap k).toRingHom =
      algebraMap (Depth.RB k) (RootBase k A) := by
    apply RingHom.ext
    intro r
    exact (rootBaseRight k A).commutes r
  rw [Polynomial.map_map, hc] at h
  apply h.trans
  rw [labelledCharacteristic, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl

/-- An actual coprime chart gives the weighted-root splitting hypotheses after base change. -/
theorem baseRoot_factor {r s : ℕ} (c : Collision.ChartData k r s A) :
    rootProduct (baseRoot k A) (fun _ => 1) Finset.univ =
      c.f₁.map (algebraMap A (RootBase k A)) * c.f₂.map (algebraMap A (RootBase k A)) := by
  have h := congrArg (Polynomial.map (algebraMap A (RootBase k A))) c.factor
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq (Depth.RB k) A (RootBase k A),
    univPoly_map_baseRoot] at h
  simpa only [rootProduct, pow_one, Polynomial.map_mul] using h

/-- The actual labelled-root chart algebra splits over admissible assignments.
The index uses the mapped first factor's degree, so this statement also covers the zero ring. -/
def baseRootSplitting {r s : ℕ} (c : Collision.ChartData k r s A) :
    RootBase k A ≃ₐ[A]
      ∀ σ : Admissible (fun _ : Fin k => 1)
        (c.f₁.map (algebraMap A (RootBase k A))).natDegree,
        FactorRing (c.f₁.map (algebraMap A (RootBase k A)))
          (c.f₂.map (algebraMap A (RootBase k A))) (baseRoot k A) (fun _ => 1) (selected σ.val) :=
  weightedSplittingAlgEquivOfCoprime
    (c.monic₁.map _) (c.monic₂.map _) (c.coprime.map (Polynomial.mapRingHom (algebraMap A (RootBase k A))))
    (baseRoot k A) (fun _ => 1) (fun _ => Nat.zero_lt_one) (baseRoot_factor k A c)

/-- Every splitting component is the original factor-identity quotient map. -/
@[simp] theorem baseRootSplitting_apply {r s : ℕ} (c : Collision.ChartData k r s A)
    (a : RootBase k A)
    (σ : Admissible (fun _ : Fin k => 1)
      (c.f₁.map (algebraMap A (RootBase k A))).natDegree) :
    baseRootSplitting k A c a σ = Ideal.Quotient.mk _ a := by
  simp only [baseRootSplitting, weightedSplittingAlgEquivOfCoprime_apply]

end KhanSL2.SymmetricFamily
