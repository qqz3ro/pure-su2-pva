module

public import KhanSL2.Factorization.ResultantChartUniversal
public import KhanSL2.Collision.JFactor
public import Mathlib.RingTheory.Flat.Localization

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial TensorProduct
namespace KhanSL2.Factorization.ChartBridge

/-- The two independent elementary coefficient rings, with their tensor product. -/
def ProductCoefficients (r s : ℕ) : Type := Depth.RB r ⊗[ℂ] Depth.RB s

instance (r s : ℕ) : CommRing (ProductCoefficients r s) :=
  inferInstanceAs (CommRing (Depth.RB r ⊗[ℂ] Depth.RB s))
instance (r s : ℕ) : Algebra ℂ (ProductCoefficients r s) :=
  inferInstanceAs (Algebra ℂ (Depth.RB r ⊗[ℂ] Depth.RB s))
instance (r s : ℕ) : Nontrivial (ProductCoefficients r s) :=
  inferInstanceAs (Nontrivial (Depth.RB r ⊗[ℂ] Depth.RB s))

def leftCoefficients (r s : ℕ) : Depth.RB r →ₐ[ℂ] ProductCoefficients r s :=
  Algebra.TensorProduct.includeLeft

def rightCoefficients (r s : ℕ) : Depth.RB s →ₐ[ℂ] ProductCoefficients r s :=
  Algebra.TensorProduct.includeRight

def firstPolynomial (r s : ℕ) : MonicDegreeEq (ProductCoefficients r s) r :=
  (universalPolynomial r).map (leftCoefficients r s).toRingHom

def secondPolynomial (r s : ℕ) : MonicDegreeEq (ProductCoefficients r s) s :=
  (universalPolynomial s).map (rightCoefficients r s).toRingHom

/-- Full elementary coefficients of the product of the two independent factors. -/
def productCoefficientsMap (r s : ℕ) : Depth.RB (r+s) →ₐ[ℂ] ProductCoefficients r s :=
  Collision.coeffHom (r+s) ((firstPolynomial r s).val * (secondPolynomial r s).val)

instance (r s : ℕ) : Algebra (Depth.RB (r+s)) (ProductCoefficients r s) :=
  (productCoefficientsMap r s).toRingHom.toAlgebra

instance (r s : ℕ) : IsScalarTower ℂ (Depth.RB (r+s)) (ProductCoefficients r s) :=
  IsScalarTower.of_algebraMap_eq fun z => ((productCoefficientsMap r s).commutes z).symm

theorem productCoefficientsMap_univPoly (r s : ℕ) :
    (Collision.univPoly (r+s)).map (productCoefficientsMap r s).toRingHom =
      (firstPolynomial r s).val * (secondPolynomial r s).val := by
  apply Collision.univPoly_map_coeffHom
    ((firstPolynomial r s).monic.mul (secondPolynomial r s).monic)
  rw [(firstPolynomial r s).monic.natDegree_mul (secondPolynomial r s).monic]
  simp only [MonicDegreeEq.natDegree]

/-- The actual resultant in the product coefficient ring. -/
def productResultant (r s : ℕ) : ProductCoefficients r s :=
  Polynomial.resultant (firstPolynomial r s).val (secondPolynomial r s).val

abbrev ProductChart (r s : ℕ) := Localization.Away (productResultant r s)

def firstOnProductChart (r s : ℕ) : MonicDegreeEq (ProductChart r s) r :=
  (firstPolynomial r s).map (algebraMap (ProductCoefficients r s) (ProductChart r s))

def secondOnProductChart (r s : ℕ) : MonicDegreeEq (ProductChart r s) s :=
  (secondPolynomial r s).map (algebraMap (ProductCoefficients r s) (ProductChart r s))

theorem productChart_factorization (r s : ℕ) :
    (firstOnProductChart r s).val * (secondOnProductChart r s).val =
      (Collision.univPoly (r+s)).map (algebraMap (Depth.RB (r+s)) (ProductChart r s)) := by
  change (firstPolynomial r s).val.map _ * (secondPolynomial r s).val.map _ = _
  rw [← Polynomial.map_mul,← productCoefficientsMap_univPoly,Polynomial.map_map]
  congr 1


theorem productChart_isCoprime (r s : ℕ) :
    IsCoprime (firstOnProductChart r s).val (secondOnProductChart r s).val := by
  rcases subsingleton_or_nontrivial (ProductChart r s) with h | h
  · let := h
    rw [Subsingleton.elim (firstOnProductChart r s).val 1]
    exact isCoprime_one_left
  let := h
  apply (Polynomial.isUnit_resultant_iff_isCoprime (firstOnProductChart r s).monic).mp
  change IsUnit (Polynomial.resultant
    ((firstPolynomial r s).val.map (algebraMap _ _))
    ((secondPolynomial r s).val.map (algebraMap _ _)))
  rw [(firstPolynomial r s).monic.natDegree_map,(secondPolynomial r s).monic.natDegree_map,
    Polynomial.resultant_map_map]
  exact IsLocalization.Away.algebraMap_isUnit (productResultant r s)

/-- The universal coprime ring maps to the explicit disjoint-factor localization. -/
def universalToProductChart (r s : ℕ) :
    Universal (r+s) r s rfl →ₐ[Depth.RB (r+s)] ProductChart r s :=
  (Polynomial.UniversalCoprimeFactorizationRing.homEquiv (ProductChart r s) r s rfl
    (universalPolynomial (r+s))).symm
      ⟨⟨firstOnProductChart r s,secondOnProductChart r s⟩,
        productChart_factorization r s,productChart_isCoprime r s⟩

section Evaluation
variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- Evaluate each of the two elementary coefficient lists on a specified monic factor. -/
def productEvaluation {r s : ℕ} (p : MonicDegreeEq A r) (q : MonicDegreeEq A s) :
    ProductCoefficients r s →ₐ[ℂ] A :=
  Algebra.TensorProduct.lift (Collision.coeffHom r p.val) (Collision.coeffHom s q.val)
    (fun _ _ => Commute.all _ _)

@[simp] theorem productEvaluation_left {r s : ℕ} (p : MonicDegreeEq A r)
    (q : MonicDegreeEq A s) (u : Depth.RB r) :
    productEvaluation p q (leftCoefficients r s u) = Collision.coeffHom r p.val u := by
  change Algebra.TensorProduct.lift _ _ _ (u ⊗ₜ[ℂ] 1) = _
  simp only [Algebra.TensorProduct.lift_tmul,map_one,mul_one]

@[simp] theorem productEvaluation_right {r s : ℕ} (p : MonicDegreeEq A r)
    (q : MonicDegreeEq A s) (u : Depth.RB s) :
    productEvaluation p q (rightCoefficients r s u) = Collision.coeffHom s q.val u := by
  change Algebra.TensorProduct.lift _ _ _ (1 ⊗ₜ[ℂ] u) = _
  simp only [Algebra.TensorProduct.lift_tmul,map_one,one_mul]

end Evaluation
end KhanSL2.Factorization.ChartBridge
