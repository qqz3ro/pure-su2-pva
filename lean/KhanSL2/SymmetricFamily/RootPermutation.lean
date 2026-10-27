module

public import KhanSL2.SymmetricFamily.RootAssignmentSplit
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Permuting labelled roots preserves the original coefficient action and carries
one actual factor-identity quotient to the correspondingly permuted quotient. -/

noncomputable section
open Polynomial
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization.WeightedRoots

/-- Renaming labelled roots fixes their elementary symmetric coefficients. -/
def rootPermutationAlgEquiv {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    RootPolynomial k ≃ₐ[Depth.RB k] RootPolynomial k where
  __ := (MvPolynomial.renameEquiv ℂ σ).toRingEquiv
  commutes' r := (Modules.elementaryAlgEquiv k r).property σ

@[simp] theorem rootPermutationAlgEquiv_apply {k : ℕ} (σ : Equiv.Perm (Fin k))
    (p : RootPolynomial k) :
    rootPermutationAlgEquiv σ p = MvPolynomial.rename σ
      (show MvPolynomial (Fin k) ℂ from p) := rfl

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]

/-- The actual labelled-root permutation after coefficient base change. -/
def baseRootPermutation (σ : Equiv.Perm (Fin k)) : RootBase k A ≃ₐ[A] RootBase k A :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) (rootPermutationAlgEquiv σ)

@[simp] theorem baseRootPermutation_tmul (σ : Equiv.Perm (Fin k))
    (a : A) (p : RootPolynomial k) :
    baseRootPermutation k A σ (a ⊗ₜ[Depth.RB k] p) =
      a ⊗ₜ[Depth.RB k] rootPermutationAlgEquiv σ p := by
  simp [baseRootPermutation]

@[simp] theorem baseRootPermutation_baseRoot (σ : Equiv.Perm (Fin k)) (i : Fin k) :
    baseRootPermutation k A σ (baseRoot k A i) = baseRoot k A (σ i) := by
  change baseRootPermutation k A σ (1 ⊗ₜ[Depth.RB k]
    (show RootPolynomial k from MvPolynomial.X i)) = _
  rw [baseRootPermutation_tmul]
  simp only [rootPermutationAlgEquiv_apply, MvPolynomial.rename_X]
  rfl

/-- Coefficient ideals commute with arbitrary ring homomorphisms. -/
theorem map_coefficientIdeal {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : R[X]) :
    Ideal.map f (coefficientIdeal p) = coefficientIdeal (p.map f) := by
  rw [coefficientIdeal, Ideal.map_span, coefficientIdeal, ← Set.range_comp]
  congr 1
  ext y
  simp only [Set.mem_range, Function.comp_apply, Polynomial.coeff_map]

private theorem map_compl_perm (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    Sᶜ.map σ.toEmbedding = (S.map σ.toEmbedding)ᶜ := by
  ext i
  simp only [Finset.mem_map_equiv, Finset.mem_compl]

/-- Root products are carried to products indexed by the permuted set. -/
theorem baseRootPermutation_product (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    (rootProduct (baseRoot k A) (fun _ => 1) S).map
        (baseRootPermutation k A σ).toRingHom =
      rootProduct (baseRoot k A) (fun _ => 1) (S.map σ.toEmbedding) := by
  simp only [rootProduct, pow_one, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, Finset.prod_map,
    Equiv.coe_toEmbedding]
  apply Finset.prod_congr rfl
  intro i _
  rw [show (baseRootPermutation k A σ).toRingHom (baseRoot k A i) =
    baseRoot k A (σ i) from baseRootPermutation_baseRoot k A σ i]

private theorem baseRootPermutation_factor
    (σ : Equiv.Perm (Fin k)) (f : A[X]) :
    (f.map (algebraMap A (RootBase k A))).map (baseRootPermutation k A σ).toRingHom =
      f.map (algebraMap A (RootBase k A)) := by
  rw [Polynomial.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact (baseRootPermutation k A σ).commutes a

/-- The original two factor-identity ideals transform equivariantly. -/
theorem baseRootPermutation_factorIdeal {r s : ℕ} (c : Collision.ChartData k r s A)
    (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    Ideal.map (baseRootPermutation k A σ).toRingHom
      (factorIdeal (c.f₁.map (algebraMap A (RootBase k A)))
        (c.f₂.map (algebraMap A (RootBase k A))) (baseRoot k A) (fun _ => 1) S) =
      factorIdeal (c.f₁.map (algebraMap A (RootBase k A)))
        (c.f₂.map (algebraMap A (RootBase k A))) (baseRoot k A) (fun _ => 1)
        (S.map σ.toEmbedding) := by
  simp only [factorIdeal, Ideal.map_sup, map_coefficientIdeal, Polynomial.map_sub,
    baseRootPermutation_product, baseRootPermutation_factor k A,
    map_compl_perm]

/-- Actual quotient-ring transport between permuted root assignments. -/
def rootFactorPermutation {r s : ℕ} (c : Collision.ChartData k r s A)
    (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) :
    FactorRing (c.f₁.map (algebraMap A (RootBase k A)))
      (c.f₂.map (algebraMap A (RootBase k A))) (baseRoot k A) (fun _ => 1) S ≃ₐ[A]
    FactorRing (c.f₁.map (algebraMap A (RootBase k A)))
      (c.f₂.map (algebraMap A (RootBase k A))) (baseRoot k A) (fun _ => 1)
      (S.map σ.toEmbedding) :=
  Ideal.quotientEquivAlg _ _ (baseRootPermutation k A σ)
    (baseRootPermutation_factorIdeal k A c σ S).symm

@[simp] theorem rootFactorPermutation_mk {r s : ℕ} (c : Collision.ChartData k r s A)
    (σ : Equiv.Perm (Fin k)) (S : Finset (Fin k)) (x : RootBase k A) :
    rootFactorPermutation k A c σ S (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (baseRootPermutation k A σ x) :=
  Ideal.quotientEquivAlg_mk _ _ _ x

end KhanSL2.SymmetricFamily
