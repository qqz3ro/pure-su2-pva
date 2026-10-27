module

public import KhanSL2.CESeries
public import Mathlib.Tactic.NoncommRing

@[expose] public section

/-! The concrete relative CE differential squares to zero on all finite cochains. -/

noncomputable section

namespace KhanSL2.CESeries

theorem Q_C_zero : Q (C 0) = -(PowerSeries.X * (C 1 * C 2)) := by
  rw [Q_C_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  rw [C_anticomm 2 1]
  simp only [mul_add, mul_neg, neg_neg]
  module

theorem Q_C_one : Q (C 1) = -(PowerSeries.X * (C 2 * C 0)) := by
  rw [Q_C_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  rw [C_anticomm 0 2]
  simp only [mul_add, mul_neg, neg_neg]
  module

theorem Q_C_two : Q (C 2) = -(PowerSeries.X * (C 0 * C 1)) := by
  rw [Q_C_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  rw [C_anticomm 1 0]
  simp only [mul_add, mul_neg, neg_neg]
  module

theorem Q_B_zero : Q (B 0) =
    PowerSeries.X * (C 2 * B 1 - C 1 * B 2) := by
  rw [Q_B_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  noncomm_ring

theorem Q_B_one : Q (B 1) =
    PowerSeries.X * (C 0 * B 2 - C 2 * B 0) := by
  rw [Q_B_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  noncomm_ring

theorem Q_B_two : Q (B 2) =
    PowerSeries.X * (C 1 * B 0 - C 0 * B 1) := by
  rw [Q_B_formula]
  norm_num [Fin.sum_univ_three, epsilon]
  noncomm_ring

theorem mul_X_mul (u v : Series) : u * (PowerSeries.X * v) = PowerSeries.X * (u * v) := by
  rw [← mul_assoc, (PowerSeries.commute_X u).eq, mul_assoc]

theorem C_middle_repeat (a b : Fin 3) : C a * (C b * C a) = 0 := by
  rw [← mul_assoc, C_anticomm a b, neg_mul, mul_assoc, C_sq, mul_zero, neg_zero]

theorem Q_square_C (a : Fin 3) : Q (Q (C a)) = 0 := by
  fin_cases a
  · change Q (Q (C 0)) = 0
    rw [Q_C_zero, map_neg, Q_X_mul, Q_mul, Q_C_one, Q_C_two, parity_C]
    simp only [neg_mul, mul_neg, neg_neg, mul_assoc, mul_X_mul,
      C_middle_repeat, mul_zero, add_zero, neg_zero]
  · change Q (Q (C 1)) = 0
    rw [Q_C_one, map_neg, Q_X_mul, Q_mul, Q_C_two, Q_C_zero, parity_C]
    simp only [neg_mul, mul_neg, neg_neg, mul_assoc, mul_X_mul,
      C_middle_repeat, mul_zero, add_zero, neg_zero]
  · change Q (Q (C 2)) = 0
    rw [Q_C_two, map_neg, Q_X_mul, Q_mul, Q_C_zero, Q_C_one, parity_C]
    simp only [neg_mul, mul_neg, neg_neg, mul_assoc, mul_X_mul,
      C_middle_repeat, mul_zero, add_zero, neg_zero]

theorem Q_square_B (a : Fin 3) : Q (Q (B a)) = 0 := by
  fin_cases a
  · change Q (Q (B 0)) = 0
    rw [Q_B_zero, Q_X_mul, map_sub, Q_mul, Q_mul,
      Q_C_two, Q_C_one, Q_B_one, Q_B_two, parity_C, parity_C]
    simp only [neg_mul, mul_neg, mul_sub, mul_add, sub_mul, mul_assoc, mul_X_mul]
    rw [← mul_assoc (C 2) (C 2), C_sq, zero_mul,
      ← mul_assoc (C 1) (C 1), C_sq, zero_mul]
    rw [← mul_assoc (C 1) (C 0), C_anticomm 1 0, neg_mul, mul_assoc]
    noncomm_ring
  · change Q (Q (B 1)) = 0
    rw [Q_B_one, Q_X_mul, map_sub, Q_mul, Q_mul,
      Q_C_zero, Q_C_two, Q_B_two, Q_B_zero, parity_C, parity_C]
    simp only [neg_mul, mul_neg, mul_sub, mul_add, sub_mul, mul_assoc, mul_X_mul]
    rw [← mul_assoc (C 0) (C 0), C_sq, zero_mul,
      ← mul_assoc (C 2) (C 2), C_sq, zero_mul]
    rw [← mul_assoc (C 2) (C 1), C_anticomm 2 1, neg_mul, mul_assoc]
    noncomm_ring
  · change Q (Q (B 2)) = 0
    rw [Q_B_two, Q_X_mul, map_sub, Q_mul, Q_mul,
      Q_C_one, Q_C_zero, Q_B_zero, Q_B_one, parity_C, parity_C]
    simp only [neg_mul, mul_neg, mul_sub, mul_add, sub_mul, mul_assoc, mul_X_mul]
    rw [← mul_assoc (C 1) (C 1), C_sq, zero_mul,
      ← mul_assoc (C 0) (C 0), C_sq, zero_mul]
    rw [← mul_assoc (C 0) (C 2), C_anticomm 0 2, neg_mul, mul_assoc]
    noncomm_ring

end KhanSL2.CESeries

namespace KhanSL2

theorem q_qGenerator (m : Mode) : q (qGenerator m) = 0 := by
  cases m with
  | c j a =>
    have h := congrArg (PowerSeries.coeff (R := Cochain) j) (CESeries.Q_square_C a)
    simpa using h
  | b j a =>
    have h := congrArg (PowerSeries.coeff (R := Cochain) j) (CESeries.Q_square_B a)
    simpa using h

/-- Square-zero on the actual finite cochain space, before taking invariants. -/
theorem q_square_zero (u : Cochain) : q (q u) = 0 :=
  q_square_zero_of_generators q_qGenerator u

end KhanSL2
