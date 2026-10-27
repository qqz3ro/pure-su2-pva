module

public import KhanSL2.Modules.SourceDualModel

@[expose] public section

/-! A jet-lowering identity is multiplication by the corresponding polynomial power sum. -/

noncomputable section
open scoped BigOperators

namespace KhanSL2.Modules

open SourceDual MvPolynomial

/-- The polynomial multiplier for a weighted shift of derivative indices. -/
def jetShiftPolynomial (r s m : ℕ) (c : Variables r s → ℂ) : Polynomial r s :=
  ∑ i, monomial (Finsupp.single i m) (c i)

/-- Lowering one derivative index changes total derivative degree by exactly `m`. -/
theorem degree_sub_single_add {r s : ℕ} (d : Variables r s →₀ ℕ)
    (i : Variables r s) (m : ℕ) (hi : m ≤ d i) :
    (d - Finsupp.single i m).degree + m = d.degree := by
  have h := congrArg Finsupp.degree
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi))
  simpa only [map_add, Finsupp.degree_single] using h

/-- Ordinary-jet factorials convert falling-factorial lowering to monomial multiplication. -/
theorem exponentFactorial_shift {r s : ℕ} (d : Variables r s →₀ ℕ)
    (i : Variables r s) (m : ℕ) (hi : m ≤ d i) :
    exponentFactorial d = ((d i).descFactorial m : ℂ) *
      exponentFactorial (d - Finsupp.single i m) := by
  classical
  unfold exponentFactorial
  calc
    ∏ j, (Nat.factorial (d j) : ℂ) =
        ∏ j, (if j = i then ((d i).descFactorial m : ℂ) else 1) *
          (Nat.factorial ((d - Finsupp.single i m) j) : ℂ) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp only [if_pos rfl, Finsupp.tsub_apply, Finsupp.single_eq_same]
        exact_mod_cast (Nat.factorial_mul_descFactorial hi).symm.trans (Nat.mul_comm _ _)
      · simp [hj, Finsupp.single_apply, Ne.symm hj]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

/-- A purely algebraic coefficient criterion for the action on the polynomial source dual.
Only the relevant total jet degree is required in the hypothesis. -/
theorem taylor_jet_lowering (r s N m : ℕ) (c : Variables r s → ℂ)
    (ell ell' : Module.Dual ℂ Source)
    (h : ∀ d : Variables r s →₀ ℕ, d.degree = N + m →
      ell' (exponentMonomial d) = ∑ i,
        if m ≤ d i then c i * ((d i).descFactorial m : ℂ) *
          ell (exponentMonomial (d - Finsupp.single i m)) else 0) :
    taylorPolynomial r s (N + m) ell' =
      jetShiftPolynomial r s m c * taylorPolynomial r s N ell := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_taylorPolynomial_all, jetShiftPolynomial, Finset.sum_mul, coeff_sum]
  simp only [coeff_monomial_mul', Finsupp.single_le_iff, coeff_taylorPolynomial_all]
  by_cases hd : d.degree = N + m
  · rw [if_pos hd, h d hd, div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : m ≤ d i
    · have hdeg : (d - Finsupp.single i m).degree = N := by
        have := degree_sub_single_add d i m hi
        omega
      rw [if_pos hi, if_pos hi, if_pos hdeg]
      have hfac := exponentFactorial_shift d i m hi
      have hf := exponentFactorial_ne_zero d
      have hg := exponentFactorial_ne_zero (d - Finsupp.single i m)
      field_simp [hf, hg]
      rw [hfac]
      ring
    · simp [hi]
  · rw [if_neg hd]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : m ≤ d i
    · have hdeg : (d - Finsupp.single i m).degree ≠ N := by
        have := degree_sub_single_add d i m hi
        omega
      simp [hi, hdeg]
    · simp [hi]

/-- If the requested lowering exceeds the total derivative degree, all terms vanish. -/
theorem taylor_jet_lowering_below (r s L m : ℕ) (c : Variables r s → ℂ)
    (ell ell' : Module.Dual ℂ Source) (hL : L < m)
    (h : ∀ d : Variables r s →₀ ℕ, d.degree = L →
      ell' (exponentMonomial d) = ∑ i,
        if m ≤ d i then c i * ((d i).descFactorial m : ℂ) *
          ell (exponentMonomial (d - Finsupp.single i m)) else 0) :
    taylorPolynomial r s L ell' = 0 := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [coeff_taylorPolynomial_all]
  by_cases hd : d.degree = L
  · rw [if_pos hd, h d hd]
    have hs : (∑ i, if m ≤ d i then c i * ((d i).descFactorial m : ℂ) *
        ell (exponentMonomial (d - Finsupp.single i m)) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi := Finsupp.le_degree i d
      rw [if_neg (by omega)]
    simp [hs]
  · simp [hd]
/-- The coefficient multiplicities of the two source generators. -/
def sourceRootWeight {r s : ℕ} : Variables r s → ℂ
  | .inl _ => 1
  | .inr _ => 3

/-- The jet-shift multiplier is exactly the weighted-root image of the coefficient power sum. -/
theorem jetShiftPolynomial_sourceRootWeight (r s m : ℕ) :
    jetShiftPolynomial r s m sourceRootWeight =
      (nu r s (powerSum (r + 3 * s) m) : Polynomial r s) := by
  rw [nu_powerSum]
  simp only [jetShiftPolynomial, Fintype.sum_sum_type, sourceRootWeight,
    MvPolynomial.psum, map_sum, map_pow, rename_X, X_pow_eq_monomial, rename_monomial,
    Finsupp.mapDomain_single]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hC : (3 : Polynomial r s) = C (3 : ℂ) := (C_eq_coe_nat 3).symm
  rw [hC, C_mul_monomial, mul_one]

end KhanSL2.Modules