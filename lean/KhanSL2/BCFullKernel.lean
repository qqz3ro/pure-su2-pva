module

public import KhanSL2.BCFullCE

@[expose] public section

/-! Constant normalized kernels after adjoining the zero ghost modes. -/

noncomputable section

namespace KhanSL2.FullBC

def kernelCoefficient (m n : FullMode) : ℂ :=
  if m.pairsWith n then
    (-1 : ℂ) ^ m.order /
      ((Nat.factorial m.order : ℂ) * (Nat.factorial n.order : ℂ))
  else 0

def kernel (m n : FullMode) : LambdaPolynomial FullCochain :=
  Finsupp.single (m.order + n.order) (kernelCoefficient m n • fullOne)

theorem pairsWith_of_kernelCoefficient_ne_zero (m n : FullMode)
    (h : kernelCoefficient m n ≠ 0) : m.pairsWith n := by
  by_contra hp
  simp [kernelCoefficient, hp] at h

private theorem factorial_ne_zero (j : ℕ) : (Nat.factorial j : ℂ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero j

theorem kernelCoefficient_next_left (m n : FullMode) :
    (m.translationCoefficient : ℂ) * kernelCoefficient m.next n =
      -kernelCoefficient m n := by
  simp only [kernelCoefficient, FullMode.next_pairsWith, FullMode.order_next,
    FullMode.translationCoefficient]
  split_ifs with h
  · simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    have hm := factorial_ne_zero m.order
    have hn := factorial_ne_zero n.order
    have hi : (m.order : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m.order
    push_cast
    field_simp [hm, hn, hi]
  · simp

theorem kernelCoefficient_next_right (m n : FullMode) :
    (n.translationCoefficient : ℂ) * kernelCoefficient m n.next =
      kernelCoefficient m n := by
  simp only [kernelCoefficient, FullMode.pairsWith_next, FullMode.order_next,
    FullMode.translationCoefficient]
  split_ifs with h
  · simp only [Nat.factorial_succ, Nat.cast_mul]
    have hm := factorial_ne_zero m.order
    have hn := factorial_ne_zero n.order
    have hi : (n.order : ℂ) + 1 ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n.order
    push_cast
    field_simp [hm, hn, hi]
  · simp

theorem kernel_next_left (m n : FullMode) :
    (m.translationCoefficient : ℂ) • kernel m.next n =
      -(kernel m n).shift := by
  simp only [kernel, FullMode.order_next, Finsupp.smul_single,
    LambdaPolynomial.shift_single, ← Finsupp.single_neg, smul_smul, neg_smul]
  rw [kernelCoefficient_next_left]
  simp [neg_smul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem kernel_next_right (m n : FullMode) :
    (n.translationCoefficient : ℂ) • kernel m n.next =
      (kernel m n).shift := by
  simp only [kernel, FullMode.order_next, Finsupp.smul_single,
    LambdaPolynomial.shift_single, smul_smul]
  rw [kernelCoefficient_next_right]
  congr 1

theorem kernelCoefficient_swap (m n : FullMode) :
    kernelCoefficient m n =
      (-1 : ℂ) ^ (m.order + n.order) * kernelCoefficient n m := by
  by_cases h : m.pairsWith n
  · have h' : n.pairsWith m := (FullMode.pairsWith_comm m n).mp h
    simp only [kernelCoefficient, ite_eq_left h, ite_eq_left h']
    rw [← mul_div_assoc, pow_add, mul_assoc, ← mul_pow]
    simp [mul_comm]
  · have h' : ¬ n.pairsWith m := by
      simpa only [FullMode.pairsWith_comm n m] using h
    simp [kernelCoefficient, h, h']

@[simp] theorem kernelCoefficient_inr (m n : Mode) :
    kernelCoefficient (.inr m) (.inr n) = BC.kernelCoefficient m n := by
  simp only [kernelCoefficient, BC.kernelCoefficient, FullMode.pairsWith_inr, FullMode.order]

end KhanSL2.FullBC
