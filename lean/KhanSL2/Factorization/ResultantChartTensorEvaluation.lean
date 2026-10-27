module

public import KhanSL2.Factorization.ResultantChartTensor

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial TensorProduct
namespace KhanSL2.Factorization.ChartBridge

section Evaluation
variable {A : Type*} [CommRing A] [Algebra ℂ A]

theorem productEvaluation_first {r s : ℕ} (p : MonicDegreeEq A r)
    (q : MonicDegreeEq A s) :
    (firstPolynomial r s).val.map (productEvaluation p q).toRingHom = p.val := by
  nontriviality A
  change ((Collision.univPoly r).map (leftCoefficients r s).toRingHom).map _ = _
  rw [Polynomial.map_map]
  have hm : (productEvaluation p q).toRingHom.comp (leftCoefficients r s).toRingHom =
      (Collision.coeffHom r p.val).toRingHom :=
    RingHom.ext (productEvaluation_left p q)
  rw [hm]
  exact Collision.univPoly_map_coeffHom p.monic p.natDegree

theorem productEvaluation_second {r s : ℕ} (p : MonicDegreeEq A r)
    (q : MonicDegreeEq A s) :
    (secondPolynomial r s).val.map (productEvaluation p q).toRingHom = q.val := by
  nontriviality A
  change ((Collision.univPoly s).map (rightCoefficients r s).toRingHom).map _ = _
  rw [Polynomial.map_map]
  have hm : (productEvaluation p q).toRingHom.comp (rightCoefficients r s).toRingHom =
      (Collision.coeffHom s q.val).toRingHom :=
    RingHom.ext (productEvaluation_right p q)
  rw [hm]
  exact Collision.univPoly_map_coeffHom q.monic q.natDegree

theorem productEvaluation_resultant {r s : ℕ} (p : MonicDegreeEq A r)
    (q : MonicDegreeEq A s) :
    productEvaluation p q (productResultant r s) = Polynomial.resultant p.val q.val := by
  nontriviality A
  unfold productResultant
  change (productEvaluation p q).toRingHom (Polynomial.resultant _ _) = _
  rw [← Polynomial.resultant_map_map,productEvaluation_first,productEvaluation_second]
  simp only [MonicDegreeEq.natDegree]

/-- Taking elementary coefficients of an actual universal polynomial map recovers that map. -/
theorem coeffHom_univPoly_map {n : ℕ} (φ : Depth.RB n →ₐ[ℂ] A) :
    Collision.coeffHom n ((Collision.univPoly n).map φ.toRingHom) = φ := by
  nontriviality A
  apply AlgHom.toRingHom_injective
  apply Collision.CoordSplit.ringHom_eq_of_univPoly
  · rw [Collision.univPoly_map_coeffHom ((Collision.univPoly_monic n).map _)
      (by rw [(Collision.univPoly_monic n).natDegree_map,Collision.natDegree_univPoly])]
    rw [AlgHom.toRingHom_eq_coe]
  · intro z
    change Collision.coeffHom n _ (algebraMap ℂ (Depth.RB n) z) =
      φ (algebraMap ℂ (Depth.RB n) z)
    rw [AlgHom.commutes,AlgHom.commutes]

variable {D : Type*} [CommRing D] [Algebra ℂ D]

theorem coeffHom_map (n : ℕ) (p : A[X]) (φ : A →ₐ[ℂ] D) :
    Collision.coeffHom n (p.map φ.toRingHom) = φ.comp (Collision.coeffHom n p) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [Collision.coeffHom,MvPolynomial.aeval_X,AlgHom.comp_apply,
    Collision.elemCoord,Polynomial.coeff_map,map_mul,map_pow,map_neg,map_one,
    AlgHom.toRingHom_eq_coe]
  rfl

theorem productEvaluation_map {r s : ℕ} (p : MonicDegreeEq A r)
    (q : MonicDegreeEq A s) (φ : A →ₐ[ℂ] D) :
    productEvaluation (p.map φ.toRingHom) (q.map φ.toRingHom) =
      φ.comp (productEvaluation p q) := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro x
    change productEvaluation (p.map φ.toRingHom) (q.map φ.toRingHom)
        (leftCoefficients r s x) = φ (productEvaluation p q (leftCoefficients r s x))
    rw [productEvaluation_left,productEvaluation_left]
    exact AlgHom.congr_fun (coeffHom_map r p.val φ) x
  · apply AlgHom.ext
    intro x
    change productEvaluation (p.map φ.toRingHom) (q.map φ.toRingHom)
        (rightCoefficients r s x) = φ (productEvaluation p q (rightCoefficients r s x))
    rw [productEvaluation_right,productEvaluation_right]
    exact AlgHom.congr_fun (coeffHom_map s q.val φ) x
end Evaluation

/-- Constants in the universal coprime ring use its original R_B-algebra map. -/
instance universal_complex (B r s : ℕ) (hsum : r+s=B) :
    Algebra ℂ (Universal B r s hsum) :=
  Collision.chartComplexAlgebra (B := B)

instance universal_complex_tower (B r s : ℕ) (hsum : r+s=B) :
    IsScalarTower ℂ (Depth.RB B) (Universal B r s hsum) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

abbrev universalFirst (r s : ℕ) : MonicDegreeEq (Universal (r+s) r s rfl) r :=
  Polynomial.UniversalCoprimeFactorizationRing.factor₁ r s rfl (universalPolynomial (r+s))
abbrev universalSecond (r s : ℕ) : MonicDegreeEq (Universal (r+s) r s rfl) s :=
  Polynomial.UniversalCoprimeFactorizationRing.factor₂ r s rfl (universalPolynomial (r+s))

/-- Evaluate the independent elementary lists on the universal coprime factors. -/
def productToUniversalRaw (r s : ℕ) :
    ProductCoefficients r s →ₐ[ℂ] Universal (r+s) r s rfl :=
  productEvaluation (universalFirst r s) (universalSecond r s)

theorem productToUniversalRaw_base (r s : ℕ) :
    (productToUniversalRaw r s).toRingHom.comp (productCoefficientsMap r s).toRingHom =
      algebraMap (Depth.RB (r+s)) (Universal (r+s) r s rfl) := by
  apply Collision.CoordSplit.ringHom_eq_of_univPoly
  · rw [← Polynomial.map_map,productCoefficientsMap_univPoly,Polynomial.map_mul]
    change (firstPolynomial r s).val.map
        (productEvaluation (universalFirst r s) (universalSecond r s)).toRingHom *
      (secondPolynomial r s).val.map
        (productEvaluation (universalFirst r s) (universalSecond r s)).toRingHom = _
    rw [productEvaluation_first,productEvaluation_second]
    exact Polynomial.UniversalCoprimeFactorizationRing.factor₁_mul_factor₂ r s rfl _
  · intro z
    change productToUniversalRaw r s (productCoefficientsMap r s (algebraMap ℂ (Depth.RB (r+s)) z)) = _
    rw [AlgHom.commutes,AlgHom.commutes]
    rfl

/-- The evaluation preserves the ORIGINAL total coefficient-ring action. -/
def productToUniversal (r s : ℕ) :
    ProductCoefficients r s →ₐ[Depth.RB (r+s)] Universal (r+s) r s rfl where
  __ := (productToUniversalRaw r s).toRingHom
  commutes' a := RingHom.congr_fun (productToUniversalRaw_base r s) a

theorem productToUniversal_resultant_isUnit (r s : ℕ) :
    IsUnit (productToUniversal r s (productResultant r s)) := by
  change IsUnit (productEvaluation (universalFirst r s) (universalSecond r s) _)
  rw [productEvaluation_resultant]
  exact (Polynomial.isUnit_resultant_iff_isCoprime (universalFirst r s).monic).mpr
    (Polynomial.UniversalCoprimeFactorizationRing.isCoprime_factor₁_factor₂ r s rfl _)

/-- The inverse-direction morphism from the explicit resultant localization. -/
def productChartToUniversal (r s : ℕ) :
    ProductChart r s →ₐ[Depth.RB (r+s)] Universal (r+s) r s rfl :=
  IsLocalization.Away.liftAlgHom (productResultant r s) (f := productToUniversal r s)
    (productToUniversal_resultant_isUnit r s)

@[simp] theorem productChartToUniversal_algebraMap (r s : ℕ) (a : ProductCoefficients r s) :
    productChartToUniversal r s (algebraMap (ProductCoefficients r s) (ProductChart r s) a) =
      productToUniversal r s a :=
  IsLocalization.Away.lift_eq (productResultant r s) (productToUniversal_resultant_isUnit r s) a

end KhanSL2.Factorization.ChartBridge
