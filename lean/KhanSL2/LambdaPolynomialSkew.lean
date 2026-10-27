module

public import KhanSL2.LambdaPolynomialLemmas
public import Mathlib.Tactic.Module
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Skew substitution by `-lambda - partial`. -/

noncomputable section

namespace KhanSL2.LambdaPolynomial

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

@[simp] theorem mapCoefficients_sub (f : Module.End ℂ A)
    (p q : LambdaPolynomial A) :
    mapCoefficients f (p - q) = mapCoefficients f p - mapCoefficients f q := by
  simp only [sub_eq_add_neg, mapCoefficients_add, mapCoefficients_neg]

private theorem pow_commute_apply (f : Module.End ℂ A) (n : ℕ) (a : A) :
    (f ^ n) (f a) = f ((f ^ n) a) := by
  change ((f ^ n) * f) a = (f * (f ^ n)) a
  rw [← pow_succ, ← pow_succ']

theorem skew_single_apply (f : Module.End ℂ A) (n j : ℕ) (a : A) :
    minusVariableMinusTranslation f (Finsupp.single n a) j =
      ((-1 : ℂ) ^ n * (Nat.choose n j : ℂ)) • ((f ^ (n - j)) a) := by
  rw [skew_single]
  by_cases h : j ≤ n
  · simp [Finset.sum_apply', Finsupp.single_apply, h, Nat.lt_succ_iff]
  · have hn : n < j := Nat.lt_of_not_ge h
    simp [Finset.sum_apply', Finsupp.single_apply, h, Nat.lt_succ_iff,
      Nat.choose_eq_zero_of_lt hn]

theorem skew_mapCoefficients (f : Module.End ℂ A) (p : LambdaPolynomial A) :
    minusVariableMinusTranslation f (mapCoefficients f p) =
      mapCoefficients f (minusVariableMinusTranslation f p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n a =>
    ext j
    simp only [mapCoefficients_single, skew_single_apply, mapCoefficients_apply,
      map_smul]
    congr 1
    exact pow_commute_apply f (n - j) a

/-- Skew substitution also commutes with any coefficient endomorphism that
commutes with translation. -/
theorem skew_mapCoefficients_of_commute (f g : Module.End ℂ A)
    (hfg : ∀ a, f (g a) = g (f a)) (p : LambdaPolynomial A) :
    minusVariableMinusTranslation f (mapCoefficients g p) =
      mapCoefficients g (minusVariableMinusTranslation f p) := by
  have hp : ∀ n a, (f ^ n) (g a) = g ((f ^ n) a) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n hn =>
      intro a
      simp [pow_succ', Module.End.mul_apply, hn, hfg]
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n a =>
    ext j
    simp only [mapCoefficients_single, skew_single_apply, mapCoefficients_apply,
      map_smul, hp]

theorem skew_single_succ (f : Module.End ℂ A) (n : ℕ) (a : A) :
    minusVariableMinusTranslation f (Finsupp.single (n + 1) a) =
      -shift (minusVariableMinusTranslation f (Finsupp.single n a)) -
        mapCoefficients f (minusVariableMinusTranslation f (Finsupp.single n a)) := by
  ext j
  cases j with
  | zero =>
    simp [skew_single_apply, pow_succ, Module.End.mul_apply, neg_smul,
      pow_commute_apply]
  | succ j =>
    simp only [Finsupp.sub_apply, Finsupp.neg_apply, shift_apply_succ,
      mapCoefficients_apply, skew_single_apply, Nat.succ_eq_add_one,
      Nat.add_sub_add_right, map_smul]
    by_cases hj : j < n
    · have he : n - (j + 1) + 1 = n - j := by omega
      have hf : f ((f ^ (n - (j + 1))) a) = (f ^ (n - j)) a := by
        rw [← Module.End.mul_apply, ← pow_succ', he]
      rw [hf, Nat.choose_succ_succ', Nat.cast_add, pow_succ]
      module
    · by_cases heq : j = n
      · subst j
        simp [Nat.choose_eq_zero_of_lt, pow_succ, neg_smul]
      · have hnj : n < j := by omega
        have hnj' : n < j + 1 := by omega
        simp [Nat.choose_eq_zero_of_lt hnj, Nat.choose_eq_zero_of_lt hnj',
          Nat.choose_eq_zero_of_lt (Nat.add_lt_add_right hnj 1)]

theorem skew_shift (f : Module.End ℂ A) (p : LambdaPolynomial A) :
    minusVariableMinusTranslation f (shift p) =
      -shift (minusVariableMinusTranslation f p) -
        mapCoefficients f (minusVariableMinusTranslation f p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp [hp, hq]
    abel
  | single n a =>
    simpa only [shift_single] using skew_single_succ f n a

theorem skew_involutive (f : Module.End ℂ A) (p : LambdaPolynomial A) :
    minusVariableMinusTranslation f (minusVariableMinusTranslation f p) = p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n a =>
    induction n with
    | zero => simp [skew_single]
    | succ n hn =>
      rw [show Finsupp.single (n + 1) a = shift (Finsupp.single n a) from
        (shift_single n a).symm, skew_shift]
      simp only [sub_eq_add_neg, skew_add, skew_neg, skew_shift,
        skew_mapCoefficients, hn]
      abel

end KhanSL2.LambdaPolynomial
