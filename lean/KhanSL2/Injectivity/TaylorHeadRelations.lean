module

public import KhanSL2.Injectivity.TaylorCoefficients
public import KhanSL2.Injectivity.DiagonalCoefficients
public import KhanSL2.Injectivity.TaylorJetConvolution

@[expose] public section

/-! The XX diagonal relation, with the two selected even factors at the front. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.SourceDual

open Source Injectivity MvPolynomial

def firstX (r s : ℕ) : Variables (r + 2) s := Sum.inl 0
def secondX (r s : ℕ) : Variables (r + 2) s := Sum.inl (Fin.succ 0)

theorem firstX_ne_secondX (r s : ℕ) : firstX r s ≠ secondX r s := by
  simp [firstX, secondX]

theorem fin_succ_succ_ne_one {r : ℕ} (i : Fin r) : i.succ.succ ≠ (1 : Fin (r + 2)) := by
  have h : i.succ.succ ≠ Fin.succ (0 : Fin (r + 1)) := by
    intro hi
    exact Fin.succ_ne_zero i (Fin.succ_inj.mp hi)
  simpa using h

def dropXX {r s : ℕ} (d : Variables (r + 2) s →₀ ℕ) : Variables r s →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm <| Sum.elim
    (fun i => d (Sum.inl i.succ.succ)) (fun i => d (Sum.inr i))

@[simp] theorem dropXX_inl {r s : ℕ} (d : Variables (r + 2) s →₀ ℕ) (i : Fin r) :
    dropXX d (Sum.inl i) = d (Sum.inl i.succ.succ) := by simp [dropXX]

@[simp] theorem dropXX_inr {r s : ℕ} (d : Variables (r + 2) s →₀ ℕ) (i : Fin s) :
    dropXX d (Sum.inr i) = d (Sum.inr i) := by simp [dropXX]

theorem exponentMonomial_headXX {r s : ℕ} (d : Variables (r + 2) s →₀ ℕ) :
    exponentMonomial d =
      (Source.X (d (firstX r s)) * Source.X (d (secondX r s))) *
        exponentMonomial (dropXX d) := by
  simp [exponentMonomial, jetMonomial, firstX, secondX, List.ofFn_succ,
    xProduct_cons, mul_assoc]

theorem exponentFactorial_headXX {r s : ℕ} (d : Variables (r + 2) s →₀ ℕ) :
    exponentFactorial d =
      (Nat.factorial (d (firstX r s)) : ℂ) *
        (Nat.factorial (d (secondX r s)) : ℂ) * exponentFactorial (dropXX d) := by
  simp only [exponentFactorial, Fintype.prod_sum_type, Fin.prod_univ_succ,
    firstX, secondX, dropXX_inl, dropXX_inr]
  ring

theorem degree_headXX {r s : ℕ} (d : Variables (r + 2) s →₀ ℕ) :
    d.degree = d (firstX r s) + d (secondX r s) + (dropXX d).degree := by
  simp only [Finsupp.degree_eq_sum, Fintype.sum_sum_type, Fin.sum_univ_succ,
    firstX, secondX, dropXX_inl, dropXX_inr]
  omega

@[simp] theorem splitExponent_firstX {r s : ℕ}
    (d : Variables (r + 2) s →₀ ℕ) (a b : ℕ) :
    splitExponent d (firstX r s) (secondX r s) a b (firstX r s) = a := by
  simp [splitExponent, Finsupp.update_apply, firstX_ne_secondX]

@[simp] theorem splitExponent_secondX {r s : ℕ}
    (d : Variables (r + 2) s →₀ ℕ) (a b : ℕ) :
    splitExponent d (firstX r s) (secondX r s) a b (secondX r s) = b := by
  simp [splitExponent, Finsupp.update_apply]

@[simp] theorem dropXX_splitExponent {r s : ℕ}
    (d : Variables (r + 2) s →₀ ℕ) (a b : ℕ) :
    dropXX (splitExponent d (firstX r s) (secondX r s) a b) = dropXX d := by
  ext i
  rcases i with i | i
  · simp [splitExponent, Finsupp.update_apply, firstX, secondX, fin_succ_succ_ne_one i]
  · simp [splitExponent, Finsupp.update_apply, firstX, secondX]

theorem degree_splitExponent_headXX {r s : ℕ}
    (d : Variables (r + 2) s →₀ ℕ) (hd : d (firstX r s) = 0)
    (a b : ℕ) (hab : a + b = d (secondX r s)) :
    (splitExponent d (firstX r s) (secondX r s) a b).degree = d.degree := by
  rw [degree_headXX, splitExponent_firstX, splitExponent_secondX,
    dropXX_splitExponent, hab, degree_headXX d, hd, zero_add]

theorem taylorPolynomial_diagonal_headXX_eq_zero (r s N : ℕ)
    (ell : Source →ₗ[ℂ] ℂ) :
    diagonal (firstX r s) (secondX r s) (taylorPolynomial (r + 2) s N ell) = 0 := by
  apply diagonal_eq_zero_of_coefficient_convolutions _ _ (firstX_ne_secondX r s)
  intro d hd
  by_cases hdegree : d.degree = N
  · convert factorial_convolution_XX ell (d (secondX r s))
      (exponentMonomial (dropXX d)) (exponentFactorial (dropXX d)) using 1
    apply Finset.sum_congr rfl
    intro ab hab
    rw [coeff_taylorPolynomial_all,
      degree_splitExponent_headXX d hd ab.1 ab.2 (Finset.mem_antidiagonal.mp hab),
      if_pos hdegree, exponentMonomial_headXX, exponentFactorial_headXX]
    simp only [splitExponent_firstX, splitExponent_secondX, dropXX_splitExponent]
  · apply Finset.sum_eq_zero
    intro ab hab
    rw [coeff_taylorPolynomial_all,
      degree_splitExponent_headXX d hd ab.1 ab.2 (Finset.mem_antidiagonal.mp hab),
      if_neg hdegree]

end KhanSL2.SourceDual
