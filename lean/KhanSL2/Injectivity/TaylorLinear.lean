module

public import KhanSL2.Injectivity.TaylorCoefficients

@[expose] public section

noncomputable section
open scoped BigOperators

namespace KhanSL2.SourceDual

def taylorPolynomialLinear (r s N : ℕ) :
    (Source →ₗ[ℂ] ℂ) →ₗ[ℂ] MvPolynomial (Variables r s) ℂ where
  toFun := taylorPolynomial r s N
  map_add' ell m := by
    classical
    simp only [taylorPolynomial, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : indexWeight a = N <;> simp [ha, add_div]
  map_smul' c ell := by
    classical
    simp only [taylorPolynomial, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : indexWeight a = N <;> simp [ha, mul_div_assoc, MvPolynomial.smul_monomial, smul_eq_mul]

@[simp] theorem taylorPolynomialLinear_apply (r s N : ℕ) (ell : Source →ₗ[ℂ] ℂ) :
    taylorPolynomialLinear r s N ell = taylorPolynomial r s N ell := rfl

end KhanSL2.SourceDual
