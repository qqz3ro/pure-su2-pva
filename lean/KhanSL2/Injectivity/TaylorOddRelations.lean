module

public import KhanSL2.Injectivity.TaylorMixedRelations

@[expose] public section

/-! The first normal derivative on an odd diagonal, from the source relation Y ∂Y = 0. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.SourceDual

open Source Injectivity MvPolynomial

def firstY (r s : ℕ) : Variables r (s + 2) := Sum.inr 0
def secondY (r s : ℕ) : Variables r (s + 2) := Sum.inr (Fin.succ 0)

theorem firstY_ne_secondY (r s : ℕ) : firstY r s ≠ secondY r s := by
  simp [firstY, secondY]

def dropYY {r s : ℕ} (d : Variables r (s + 2) →₀ ℕ) : Variables r s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm <| Sum.elim
    (fun i => d (Sum.inl i)) (fun i => d (Sum.inr i.succ.succ))

@[simp] theorem dropYY_inl {r s : ℕ} (d : Variables r (s + 2) →₀ ℕ) (i : Fin r) :
    dropYY d (Sum.inl i) = d (Sum.inl i) := by simp [dropYY]

@[simp] theorem dropYY_inr {r s : ℕ} (d : Variables r (s + 2) →₀ ℕ) (i : Fin s) :
    dropYY d (Sum.inr i) = d (Sum.inr i.succ.succ) := by simp [dropYY]

theorem exponentMonomial_headYY {r s : ℕ} (d : Variables r (s + 2) →₀ ℕ) :
    exponentMonomial d =
      (Source.Y (d (firstY r s)) * Source.Y (d (secondY r s))) *
        exponentMonomial (dropYY d) := by
  have h := yProduct_mul_xProduct [d (firstY r s), d (secondY r s)]
    (List.ofFn fun i => d (Sum.inl i))
  simp only [yProduct_cons, yProduct_nil, mul_one] at h
  simp only [exponentMonomial, jetMonomial, firstY, secondY, List.ofFn_succ,
    yProduct_cons, dropYY_inl, dropYY_inr] at h ⊢
  rw [← mul_assoc (Source.Y _) (Source.Y _), ← mul_assoc, ← h]
  simp only [mul_assoc]

theorem exponentFactorial_headYY {r s : ℕ} (d : Variables r (s + 2) →₀ ℕ) :
    exponentFactorial d =
      (Nat.factorial (d (firstY r s)) : ℂ) *
        (Nat.factorial (d (secondY r s)) : ℂ) * exponentFactorial (dropYY d) := by
  simp only [exponentFactorial, Fintype.prod_sum_type, Fin.prod_univ_succ,
    firstY, secondY, dropYY_inl, dropYY_inr]
  ring

theorem degree_headYY {r s : ℕ} (d : Variables r (s + 2) →₀ ℕ) :
    d.degree = d (firstY r s) + d (secondY r s) + (dropYY d).degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Fin.sum_univ_succ,
    firstY, secondY, dropYY_inl, dropYY_inr]
  omega

@[simp] theorem splitExponent_firstY {r s : ℕ}
    (d : Variables r (s + 2) →₀ ℕ) (a b : ℕ) :
    splitExponent d (firstY r s) (secondY r s) a b (firstY r s) = a := by
  simp [splitExponent, Finsupp.update_apply, firstY_ne_secondY]

@[simp] theorem splitExponent_secondY {r s : ℕ}
    (d : Variables r (s + 2) →₀ ℕ) (a b : ℕ) :
    splitExponent d (firstY r s) (secondY r s) a b (secondY r s) = b := by
  simp [splitExponent, Finsupp.update_apply]

@[simp] theorem dropYY_splitExponent {r s : ℕ}
    (d : Variables r (s + 2) →₀ ℕ) (a b : ℕ) :
    dropYY (splitExponent d (firstY r s) (secondY r s) a b) = dropYY d := by
  ext i
  rcases i with i | i
  · simp [splitExponent, Finsupp.update_apply, firstY, secondY]
  · simp [splitExponent, Finsupp.update_apply, firstY, secondY, fin_succ_succ_ne_one i]

theorem degree_splitExponent_headYY {r s : ℕ}
    (d : Variables r (s + 2) →₀ ℕ) (hd : d (firstY r s) = 0)
    (a b : ℕ) (hab : a + b = d (secondY r s)) :
    (splitExponent d (firstY r s) (secondY r s) a b).degree = d.degree := by
  rw [degree_headYY, splitExponent_firstY, splitExponent_secondY,
    dropYY_splitExponent, hab, degree_headYY d, hd, zero_add]

theorem taylorPolynomial_diagonal_pderiv_headYY_eq_zero (r s N : ℕ)
    (ell : Source →ₗ[ℂ] ℂ) :
    diagonal (firstY r s) (secondY r s)
      (pderiv (firstY r s) (taylorPolynomial r (s + 2) N ell)) = 0 := by
  apply diagonal_eq_zero_of_coefficient_convolutions _ _ (firstY_ne_secondY r s)
  intro d hd
  have hdegree (a b : ℕ) (hab : a + b = d (secondY r s)) :
      (splitExponent d (firstY r s) (secondY r s) (a + 1) b).degree = d.degree + 1 := by
    rw [← splitExponent_add_single_left d _ _ (firstY_ne_secondY r s) a b,
      map_add, degree_splitExponent_headYY d hd a b hab]
    simp
  by_cases hN : d.degree + 1 = N
  · convert factorial_convolution_dYY ell (d (secondY r s))
      (exponentMonomial (dropYY d)) (exponentFactorial (dropYY d)) using 1
    apply Finset.sum_congr rfl
    intro ab hab
    rw [coeff_pderiv, splitExponent_add_single_left d _ _ (firstY_ne_secondY r s),
      coeff_taylorPolynomial_all, hdegree ab.1 ab.2 (Finset.mem_antidiagonal.mp hab),
      if_pos hN, exponentMonomial_headYY, exponentFactorial_headYY]
    simp only [splitExponent_firstY, splitExponent_secondY, dropYY_splitExponent,
      Nat.cast_add, Nat.cast_one]
    exact cancel_next_factorial _ _ _ _ (exponentFactorial_ne_zero _)
  · apply Finset.sum_eq_zero
    intro ab hab
    rw [coeff_pderiv, splitExponent_add_single_left d _ _ (firstY_ne_secondY r s),
      coeff_taylorPolynomial_all, hdegree ab.1 ab.2 (Finset.mem_antidiagonal.mp hab),
      if_neg hN, zero_mul]

end KhanSL2.SourceDual
