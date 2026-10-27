module

public import KhanSL2.Injectivity.TaylorPolynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

/-! Homogeneity and an unrestricted exponent formula for the finite Taylor polynomial. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.SourceDual

open Source

theorem exponent_degree {r s N : ℕ} (a : TaylorIndex r s N) :
    (exponent a).degree = indexWeight a := by
  classical
  simp only [indexWeight_eq_sum, Finsupp.degree_eq_sum, exponent_apply]

theorem taylorPolynomial_homogeneous (r s N : ℕ) (ell : Source →ₗ[ℂ] ℂ) :
    (taylorPolynomial r s N ell).IsHomogeneous N := by
  classical
  unfold taylorPolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro a _
  by_cases ha : indexWeight a = N
  · rw [if_pos ha]
    exact MvPolynomial.isHomogeneous_monomial _ ((exponent_degree a).trans ha)
  · rw [if_neg ha]
    exact MvPolynomial.isHomogeneous_zero (σ := Variables r s) (R := ℂ) N

def indexOfExponent {r s N : ℕ} (d : Variables r s →₀ ℕ) (h : d.degree = N) :
    TaylorIndex r s N := fun i => ⟨d i, by have := Finsupp.le_degree i d; omega⟩

@[simp] theorem exponent_indexOfExponent {r s N : ℕ}
    (d : Variables r s →₀ ℕ) (h : d.degree = N) :
    exponent (indexOfExponent d h) = d := by
  ext i
  rfl

theorem indexWeight_indexOfExponent {r s N : ℕ}
    (d : Variables r s →₀ ℕ) (h : d.degree = N) :
    indexWeight (indexOfExponent d h) = N := by
  rw [← exponent_degree, exponent_indexOfExponent, h]

def exponentMonomial {r s : ℕ} (d : Variables r s →₀ ℕ) : Source :=
  jetMonomial (List.ofFn fun i => d (Sum.inl i)) (List.ofFn fun i => d (Sum.inr i))

def exponentFactorial {r s : ℕ} (d : Variables r s →₀ ℕ) : ℂ :=
  ∏ i, (Nat.factorial (d i) : ℂ)

theorem exponentFactorial_ne_zero {r s : ℕ} (d : Variables r s →₀ ℕ) :
    exponentFactorial d ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast Nat.factorial_ne_zero (d i)

theorem coeff_taylorPolynomial_all (r s N : ℕ) (ell : Source →ₗ[ℂ] ℂ)
    (d : Variables r s →₀ ℕ) :
    (taylorPolynomial r s N ell).coeff d =
      if d.degree = N then ell (exponentMonomial d) / exponentFactorial d else 0 := by
  classical
  by_cases hd : d.degree = N
  · rw [if_pos hd]
    have h := coeff_taylorPolynomial ell (indexOfExponent d hd)
      (indexWeight_indexOfExponent d hd)
    simpa only [exponent_indexOfExponent, indexOfExponent, xIndices, yIndices,
      jetFactorial, exponentMonomial, exponentFactorial] using h
  · rw [if_neg hd]
    exact (taylorPolynomial_homogeneous r s N ell).coeff_eq_zero hd

end KhanSL2.SourceDual
