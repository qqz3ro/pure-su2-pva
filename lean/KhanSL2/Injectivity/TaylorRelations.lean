module

public import KhanSL2.Injectivity.TaylorPolynomial
public import KhanSL2.SourceGeneration
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# Finite coefficient identities from the source relations

The iterated Leibniz rule is proved for the actual noncommutative source
algebra.  Dividing by factorials gives the convolution identities used by
diagonal specialization of the Taylor polynomial.
-/

noncomputable section

open scoped BigOperators

namespace KhanSL2.Source

theorem translation_pow_mul (n : ℕ) (a b : Source) :
    (translation ^ n) (a * b) =
      ∑ ij ∈ Finset.antidiagonal n,
        n.choose ij.1 • ((translation ^ ij.1) a * (translation ^ ij.2) b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => (translation ^ i) a * (translation ^ j) b) n]
    simp only [pow_succ', Module.End.mul_apply, ih, map_sum, map_nsmul,
      translation_mul, nsmul_add, Finset.sum_add_distrib]
    rw [add_comm, add_left_cancel_iff]
    refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
    rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hij).symm]

def dividedTranslate (n : ℕ) (a : Source) : Source :=
  ((Nat.factorial n : ℂ)⁻¹) • (translation ^ n) a

theorem dividedTranslate_mul (n : ℕ) (a b : Source) :
    dividedTranslate n (a * b) =
      ∑ ij ∈ Finset.antidiagonal n, dividedTranslate ij.1 a * dividedTranslate ij.2 b := by
  rw [dividedTranslate, translation_pow_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ⟨i, j⟩ hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  subst n
  simp only [dividedTranslate, smul_mul_smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have h : (((i + j).choose i : ℂ) * (Nat.factorial i : ℂ) *
      (Nat.factorial j : ℂ)) = (Nat.factorial (i + j) : ℂ) := by
    have hn := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
    rw [Nat.add_sub_cancel_left] at hn
    exact_mod_cast hn
  have hi : (Nat.factorial i : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (Nat.factorial j : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hn : (Nat.factorial (i + j) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i + j)
  field_simp
  simpa only [mul_assoc] using h

@[simp] theorem dividedTranslate_zero (n : ℕ) : dividedTranslate n 0 = 0 := by
  simp [dividedTranslate]

theorem convolution_eq_zero_of_mul_eq_zero (n : ℕ) {a b : Source} (h : a * b = 0) :
    (∑ ij ∈ Finset.antidiagonal n,
      dividedTranslate ij.1 a * dividedTranslate ij.2 b) = 0 := by
  rw [← dividedTranslate_mul, h, dividedTranslate_zero]

theorem dividedTranslate_X (n i : ℕ) :
    dividedTranslate n (X i) = (Nat.factorial n : ℂ)⁻¹ • X (i + n) := by
  simp [dividedTranslate]

theorem dividedTranslate_Y (n i : ℕ) :
    dividedTranslate n (Y i) = (Nat.factorial n : ℂ)⁻¹ • Y (i + n) := by
  simp [dividedTranslate]

/-- A differentiated relation remains zero after multiplication and linear evaluation. -/
theorem functional_convolution_eq_zero (ell : Source →ₗ[ℂ] ℂ) (n : ℕ)
    (left right : Source) {a b : Source} (h : a * b = 0) :
    (∑ ij ∈ Finset.antidiagonal n,
      ell (left * (dividedTranslate ij.1 a * dividedTranslate ij.2 b) * right)) = 0 := by
  rw [← map_sum, ← Finset.sum_mul, ← Finset.mul_sum,
    convolution_eq_zero_of_mul_eq_zero n h]
  simp

theorem convolution_XX (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      dividedTranslate ij.1 (X 0) * dividedTranslate ij.2 (X 0)) = 0 :=
  convolution_eq_zero_of_mul_eq_zero n X0_sq

theorem convolution_XY (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      dividedTranslate ij.1 (X 0) * dividedTranslate ij.2 (Y 0)) = 0 :=
  convolution_eq_zero_of_mul_eq_zero n X0_Y0

theorem convolution_XdY (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      dividedTranslate ij.1 (X 0) * dividedTranslate ij.2 (Y 1)) = 0 :=
  convolution_eq_zero_of_mul_eq_zero n X0_Y1

theorem convolution_YdY (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      dividedTranslate ij.1 (Y 0) * dividedTranslate ij.2 (Y 1)) = 0 :=
  convolution_eq_zero_of_mul_eq_zero n Y0_Y1

theorem X1_Y0 : X 1 * Y 0 = 0 := by
  have h := congrArg translation X0_Y0
  rw [translation_mul] at h
  simpa using h

theorem Y1_Y0 : Y 1 * Y 0 = 0 := by
  rw [Y_mul_Y, Y0_Y1, neg_zero]

/-- The normal derivative may be taken in the first variable of the pair. -/
theorem convolution_dXY (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      dividedTranslate ij.1 (X 1) * dividedTranslate ij.2 (Y 0)) = 0 :=
  convolution_eq_zero_of_mul_eq_zero n X1_Y0

theorem convolution_dYY (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      dividedTranslate ij.1 (Y 1) * dividedTranslate ij.2 (Y 0)) = 0 :=
  convolution_eq_zero_of_mul_eq_zero n Y1_Y0

end KhanSL2.Source
