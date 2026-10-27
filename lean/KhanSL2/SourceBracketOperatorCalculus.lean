module

public import KhanSL2.SourceBracketOperators
public import Mathlib.Tactic.Abel

@[expose] public section

/-! The conjugated multiplication operators act only on coefficient factors. -/

noncomputable section

namespace KhanSL2.SourceBracketOperators

open LambdaPolynomial

@[simp] theorem left_single_zero (a v : Source) :
    left a (Finsupp.single 0 v) = Finsupp.single 0 (a * v) := by
  simp [left_apply, K_apply, skew_single, sourceData]

@[simp] theorem right_single_zero (a v : Source) :
    right a (Finsupp.single 0 v) = Finsupp.single 0 (v * a) := by
  simp [right_apply, K_apply, skew_single, sourceData]

theorem left_shift (a : Source) (p : Poly) :
    left a (shift p) = shift (left a p) + left (Source.translation a) p := by
  have h := left_translation_commutator a p
  simp only [negativeShift_apply, map_neg] at h
  have h' := congrArg Neg.neg h
  simp only [neg_neg, neg_add_rev] at h'
  apply eq_of_sub_eq_zero
  have : left a (shift p) - (shift (left a p) + left (Source.translation a) p) = 0 := by
    rw [h']
    abel
  exact this

theorem right_shift (a : Source) (p : Poly) :
    right a (shift p) = shift (right a p) + right (Source.translation a) p := by
  have h := right_translation_commutator a p
  simp only [negativeShift_apply, map_neg] at h
  have h' := congrArg Neg.neg h
  simp only [neg_neg, neg_add_rev] at h'
  apply eq_of_sub_eq_zero
  have : right a (shift p) - (shift (right a p) + right (Source.translation a) p) = 0 := by
    rw [h']
    abel
  exact this

theorem left_single_succ (a v : Source) (n : ℕ) :
    left a (Finsupp.single (n + 1) v) =
      shift (left a (Finsupp.single n v)) +
        left (Source.translation a) (Finsupp.single n v) := by
  rw [← shift_single, left_shift]

theorem right_single_succ (a v : Source) (n : ℕ) :
    right a (Finsupp.single (n + 1) v) =
      shift (right a (Finsupp.single n v)) +
        right (Source.translation a) (Finsupp.single n v) := by
  rw [← shift_single, right_shift]

theorem shift_mulRight (p : Poly) (a : Source) :
    shift (mulRight sourceData p a) = mulRight sourceData (shift p) a := by
  ext n
  cases n <;> simp [sourceData]

theorem shift_mulLeft (a : Source) (p : Poly) :
    shift (mulLeft sourceData a p) = mulLeft sourceData a (shift p) := by
  ext n
  cases n <;> simp [sourceData]

theorem left_mulRight (a b : Source) (p : Poly) :
    left a (mulRight sourceData p b) =
      mulRight sourceData (left a p) b := by
  induction p using Finsupp.induction_linear generalizing a with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v =>
    induction n generalizing a with
    | zero => simp [sourceData, mul_assoc]
    | succ n ih =>
      simp only [mulRight_single, left_single_succ, mulRight_add]
      simp only [mulRight_single] at ih
      rw [ih, ih, shift_mulRight]

theorem right_mulLeft (a b : Source) (p : Poly) :
    right b (mulLeft sourceData a p) =
      mulLeft sourceData a (right b p) := by
  induction p using Finsupp.induction_linear generalizing b with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v =>
    induction n generalizing b with
    | zero => simp [sourceData, mul_assoc]
    | succ n ih =>
      simp only [mulLeft_single, right_single_succ, mulLeft_add]
      simp only [mulLeft_single] at ih
      rw [ih, ih, shift_mulLeft]

theorem rightTranslation_left (a : Source) (p : Poly) :
    rightTranslation Source.translation (left a p) =
      left a (rightTranslation Source.translation p) := by
  rw [left_apply, rightTranslation_K]
  have h : negativeShift (mulLeft sourceData a (K p)) =
      mulLeft sourceData a (negativeShift (K p)) := by
    simp only [negativeShift_apply, shift_mulLeft]
    exact ((mulLeftLinear sourceData a).map_neg (shift (K p))).symm
  rw [h, ← K_rightTranslation]
  rfl

theorem rightTranslation_right (a : Source) (p : Poly) :
    rightTranslation Source.translation (right a p) =
      right a (rightTranslation Source.translation p) := by
  rw [right_apply, rightTranslation_K]
  have h : negativeShift (mulRight sourceData (K p) a) =
      mulRight sourceData (negativeShift (K p)) a := by
    simp only [negativeShift_apply, shift_mulRight]
    exact ((mulRightLinear sourceData a).map_neg (shift (K p))).symm
  rw [h, ← K_rightTranslation]
  rfl

end KhanSL2.SourceBracketOperators
