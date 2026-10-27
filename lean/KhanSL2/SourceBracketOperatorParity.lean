module

public import KhanSL2.SourceBracketOperatorCalculus
public import KhanSL2.SourceSupercommUngraded

@[expose] public section

/-! Parity and the mixed multiplication rules for the left-bracket operators. -/

noncomputable section

namespace KhanSL2.SourceBracketOperators

open LambdaPolynomial Source

theorem parity_left (a : Source) (p : Poly) :
    mapCoefficients parity.toLinearMap (left a p) =
      left (parity a) (mapCoefficients parity.toLinearMap p) := by
  induction p using Finsupp.induction_linear generalizing a with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v =>
    induction n generalizing a with
    | zero => simp [sourceData]
    | succ n ih =>
      simp only [mapCoefficients_single] at ih ⊢
      simp only [left_single_succ, mapCoefficients_add, mapCoefficients_shift]
      rw [ih, ih, parity_translation]

theorem parity_right (a : Source) (p : Poly) :
    mapCoefficients parity.toLinearMap (right a p) =
      right (parity a) (mapCoefficients parity.toLinearMap p) := by
  induction p using Finsupp.induction_linear generalizing a with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v =>
    induction n generalizing a with
    | zero => simp [sourceData]
    | succ n ih =>
      simp only [mapCoefficients_single] at ih ⊢
      simp only [right_single_succ, mapCoefficients_add, mapCoefficients_shift]
      rw [ih, ih, parity_translation]

theorem left_mulLeft_even (a c : Source) (p : Poly) :
    left a (mulLeft sourceData (evenPart c) p) =
      mulLeft sourceData (evenPart c) (left a p) := by
  induction p using Finsupp.induction_linear generalizing a with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v =>
    induction n generalizing a with
    | zero =>
      simp only [mulLeft_single, left_single_zero]
      congr 1
      change a * (evenPart c * v) = evenPart c * (a * v)
      rw [← mul_assoc, mul_evenPart, mul_assoc]
    | succ n ih =>
      simp only [mulLeft_single] at ih ⊢
      simp only [left_single_succ, mulLeft_add]
      rw [ih, ih, shift_mulLeft]

theorem left_mulLeft_odd (a c : Source) (p : Poly) :
    left a (mulLeft sourceData (oddPart c) p) =
      mulLeft sourceData (oddPart c) (left (parity a) p) := by
  induction p using Finsupp.induction_linear generalizing a with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v =>
    induction n generalizing a with
    | zero =>
      simp only [mulLeft_single, left_single_zero]
      congr 1
      change a * (oddPart c * v) = oddPart c * (parity a * v)
      rw [← mul_assoc, mul_oddPart, mul_assoc]
    | succ n ih =>
      simp only [mulLeft_single] at ih ⊢
      simp only [left_single_succ, mulLeft_add]
      rw [ih, ih, parity_translation, shift_mulLeft]

theorem right_mulRight_even (a c : Source) (p : Poly) :
    right a (mulRight sourceData p (evenPart c)) =
      mulRight sourceData (right a p) (evenPart c) := by
  induction p using Finsupp.induction_linear generalizing a with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v =>
    induction n generalizing a with
    | zero =>
      simp only [mulRight_single, right_single_zero]
      congr 1
      change (v * evenPart c) * a = (v * a) * evenPart c
      rw [mul_assoc, ← mul_evenPart a c, ← mul_assoc]
    | succ n ih =>
      simp only [mulRight_single] at ih ⊢
      simp only [right_single_succ, mulRight_add]
      rw [ih, ih, shift_mulRight]

theorem right_mulRight_odd (a c : Source) (p : Poly) :
    right a (mulRight sourceData p (oddPart c)) =
      mulRight sourceData (right (parity a) p) (oddPart c) := by
  induction p using Finsupp.induction_linear generalizing a with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n v =>
    induction n generalizing a with
    | zero =>
      simp only [mulRight_single, right_single_zero]
      congr 1
      change (v * oddPart c) * a = (v * parity a) * oddPart c
      rw [mul_assoc, ← parity_parity a, ← mul_oddPart (parity a) c,
        parity_parity, ← mul_assoc]
    | succ n ih =>
      simp only [mulRight_single] at ih ⊢
      simp only [right_single_succ, mulRight_add]
      rw [ih, ih, parity_translation, shift_mulRight]

end KhanSL2.SourceBracketOperators
