module

public import KhanSL2.Injectivity.TaylorHeadRelations

@[expose] public section

/-! The mixed diagonal and its first normal derivative from the two mixed source relations. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.Source

theorem xProduct_mul_Y (xs : List ℕ) (n : ℕ) : xProduct xs * Y n = Y n * xProduct xs := by
  simpa using (yProduct_mul_xProduct [n] xs).symm

end KhanSL2.Source

namespace KhanSL2.SourceDual

open Source Injectivity MvPolynomial

def mixedX (r s : ℕ) : Variables (r + 1) (s + 1) := Sum.inl 0
def mixedY (r s : ℕ) : Variables (r + 1) (s + 1) := Sum.inr 0

theorem mixedX_ne_mixedY (r s : ℕ) : mixedX r s ≠ mixedY r s := by
  simp [mixedX, mixedY]

def dropXY {r s : ℕ} (d : Variables (r + 1) (s + 1) →₀ ℕ) : Variables r s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm <| Sum.elim
    (fun i => d (Sum.inl i.succ)) (fun i => d (Sum.inr i.succ))

@[simp] theorem dropXY_inl {r s : ℕ}
    (d : Variables (r + 1) (s + 1) →₀ ℕ) (i : Fin r) :
    dropXY d (Sum.inl i) = d (Sum.inl i.succ) := by simp [dropXY]

@[simp] theorem dropXY_inr {r s : ℕ}
    (d : Variables (r + 1) (s + 1) →₀ ℕ) (i : Fin s) :
    dropXY d (Sum.inr i) = d (Sum.inr i.succ) := by simp [dropXY]

theorem exponentMonomial_headXY {r s : ℕ} (d : Variables (r + 1) (s + 1) →₀ ℕ) :
    exponentMonomial d =
      (Source.X (d (mixedX r s)) * Source.Y (d (mixedY r s))) *
        exponentMonomial (dropXY d) := by
  simp only [exponentMonomial, jetMonomial, mixedX, mixedY, List.ofFn_succ,
    xProduct_cons, yProduct_cons, dropXY_inl, dropXY_inr]
  rw [mul_assoc, ← mul_assoc (xProduct _) (Source.Y _), xProduct_mul_Y]
  simp only [mul_assoc]

theorem exponentFactorial_headXY {r s : ℕ} (d : Variables (r + 1) (s + 1) →₀ ℕ) :
    exponentFactorial d =
      (Nat.factorial (d (mixedX r s)) : ℂ) *
        (Nat.factorial (d (mixedY r s)) : ℂ) * exponentFactorial (dropXY d) := by
  simp only [exponentFactorial, Fintype.prod_sum_type, Fin.prod_univ_succ,
    mixedX, mixedY, dropXY_inl, dropXY_inr]
  ring

theorem degree_headXY {r s : ℕ} (d : Variables (r + 1) (s + 1) →₀ ℕ) :
    d.degree = d (mixedX r s) + d (mixedY r s) + (dropXY d).degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Fin.sum_univ_succ,
    mixedX, mixedY, dropXY_inl, dropXY_inr]
  omega

@[simp] theorem splitExponent_mixedX {r s : ℕ}
    (d : Variables (r + 1) (s + 1) →₀ ℕ) (a b : ℕ) :
    splitExponent d (mixedX r s) (mixedY r s) a b (mixedX r s) = a := by
  simp [splitExponent, Finsupp.update_apply, mixedX_ne_mixedY]

@[simp] theorem splitExponent_mixedY {r s : ℕ}
    (d : Variables (r + 1) (s + 1) →₀ ℕ) (a b : ℕ) :
    splitExponent d (mixedX r s) (mixedY r s) a b (mixedY r s) = b := by
  simp [splitExponent, Finsupp.update_apply]

@[simp] theorem dropXY_splitExponent {r s : ℕ}
    (d : Variables (r + 1) (s + 1) →₀ ℕ) (a b : ℕ) :
    dropXY (splitExponent d (mixedX r s) (mixedY r s) a b) = dropXY d := by
  ext i
  rcases i with i | i <;>
    simp [splitExponent, Finsupp.update_apply, mixedX, mixedY]

theorem degree_splitExponent_headXY {r s : ℕ}
    (d : Variables (r + 1) (s + 1) →₀ ℕ) (hd : d (mixedX r s) = 0)
    (a b : ℕ) (hab : a + b = d (mixedY r s)) :
    (splitExponent d (mixedX r s) (mixedY r s) a b).degree = d.degree := by
  rw [degree_headXY, splitExponent_mixedX, splitExponent_mixedY,
    dropXY_splitExponent, hab, degree_headXY d, hd, zero_add]

theorem taylorPolynomial_diagonal_headXY_eq_zero (r s N : ℕ)
    (ell : Source →ₗ[ℂ] ℂ) :
    diagonal (mixedX r s) (mixedY r s) (taylorPolynomial (r + 1) (s + 1) N ell) = 0 := by
  apply diagonal_eq_zero_of_coefficient_convolutions _ _ (mixedX_ne_mixedY r s)
  intro d hd
  by_cases hdegree : d.degree = N
  · convert factorial_convolution_XY ell (d (mixedY r s))
      (exponentMonomial (dropXY d)) (exponentFactorial (dropXY d)) using 1
    apply Finset.sum_congr rfl
    intro ab hab
    rw [coeff_taylorPolynomial_all,
      degree_splitExponent_headXY d hd ab.1 ab.2 (Finset.mem_antidiagonal.mp hab),
      if_pos hdegree, exponentMonomial_headXY, exponentFactorial_headXY]
    simp only [splitExponent_mixedX, splitExponent_mixedY, dropXY_splitExponent]
  · apply Finset.sum_eq_zero
    intro ab hab
    rw [coeff_taylorPolynomial_all,
      degree_splitExponent_headXY d hd ab.1 ab.2 (Finset.mem_antidiagonal.mp hab),
      if_neg hdegree]

theorem cancel_next_factorial (A C : ℂ) (a b : ℕ) (hC : C ≠ 0) :
    A / ((Nat.factorial (a + 1) : ℂ) * (Nat.factorial b : ℂ) * C) * ((a : ℂ) + 1) =
      A / ((Nat.factorial a : ℂ) * (Nat.factorial b : ℂ) * C) := by
  have ha : (Nat.factorial a : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hb : (Nat.factorial b : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero b
  have hn : (a : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem taylorPolynomial_diagonal_pderiv_headXY_eq_zero (r s N : ℕ)
    (ell : Source →ₗ[ℂ] ℂ) :
    diagonal (mixedX r s) (mixedY r s)
      (pderiv (mixedX r s) (taylorPolynomial (r + 1) (s + 1) N ell)) = 0 := by
  apply diagonal_eq_zero_of_coefficient_convolutions _ _ (mixedX_ne_mixedY r s)
  intro d hd
  have hdegree (a b : ℕ) (hab : a + b = d (mixedY r s)) :
      (splitExponent d (mixedX r s) (mixedY r s) (a + 1) b).degree = d.degree + 1 := by
    rw [← splitExponent_add_single_left d _ _ (mixedX_ne_mixedY r s) a b,
      map_add, degree_splitExponent_headXY d hd a b hab]
    simp
  by_cases hN : d.degree + 1 = N
  · convert factorial_convolution_dXY ell (d (mixedY r s))
      (exponentMonomial (dropXY d)) (exponentFactorial (dropXY d)) using 1
    apply Finset.sum_congr rfl
    intro ab hab
    rw [coeff_pderiv, splitExponent_add_single_left d _ _ (mixedX_ne_mixedY r s),
      coeff_taylorPolynomial_all, hdegree ab.1 ab.2 (Finset.mem_antidiagonal.mp hab),
      if_pos hN, exponentMonomial_headXY, exponentFactorial_headXY]
    simp only [splitExponent_mixedX, splitExponent_mixedY, dropXY_splitExponent,
      Nat.cast_add, Nat.cast_one]
    exact cancel_next_factorial _ _ _ _ (exponentFactorial_ne_zero _)
  · apply Finset.sum_eq_zero
    intro ab hab
    rw [coeff_pderiv, splitExponent_add_single_left d _ _ (mixedX_ne_mixedY r s),
      coeff_taylorPolynomial_all, hdegree ab.1 ab.2 (Finset.mem_antidiagonal.mp hab),
      if_neg hN, zero_mul]

end KhanSL2.SourceDual
