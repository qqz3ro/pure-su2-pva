module

public import KhanSL2.Injectivity.OrderedProducts
public import KhanSL2.Injectivity.FinitePairing
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace KhanSL2.FiniteExterior

open Finset KhanSL2.Injectivity

variable {α : Type*} [DecidableEq α] [GeneratorOrder α]

def generatorWord {n : ℕ} (a : Fin n → α) : Exterior α :=
  orderedProduct (fun i => generator (a i))

@[simp] theorem generatorWord_zero (a : Fin 0 → α) : generatorWord a = 1 := by
  simp [generatorWord]

theorem generatorWord_succ {n : ℕ} (a : Fin (n + 1) → α) :
    generatorWord a = generator (a 0) * generatorWord (Fin.tail a) := by
  rw [generatorWord, orderedProduct_succ]
  rfl

theorem generatorWord_remove_zero {n : ℕ} (b : Fin (n + 1) → α) :
    generatorWord ((0 : Fin (n + 1)).removeNth b) = generatorWord (Fin.tail b) := by
  rw [Fin.removeNth_zero]

theorem generatorWord_remove_succ {n : ℕ} (b : Fin (n + 2) → α) (j : Fin (n + 1)) :
    generatorWord (j.succ.removeNth b) =
      generator (b 0) * generatorWord (j.removeNth (Fin.tail b)) := by
  rw [generatorWord_succ]
  have hzero : (j.succ.removeNth b) 0 = b 0 := rfl
  have htail : Fin.tail (j.succ.removeNth b) = j.removeNth (Fin.tail b) := by
    funext i
    simp [Fin.tail_def, Fin.removeNth, Fin.succ_succAbove_succ]
  rw [hzero, htail]

theorem contraction_generatorWord (a : α) {n : ℕ} (b : Fin (n + 1) → α) :
    contraction GeneratorOrder.code a (generatorWord b) =
      ∑ j : Fin (n + 1), (-1 : ℂ) ^ (j : ℕ) •
        (if a = b j then generatorWord (j.removeNth b) else 0) := by
  induction n with
  | zero =>
    rw [generatorWord_succ]
    change contraction GeneratorOrder.code a
      (wedge GeneratorOrder.code (generator (b 0)) (generatorWord (Fin.tail b))) = _
    rw [contraction_generator_wedge GeneratorOrder.code GeneratorOrder.code_injective]
    by_cases h : a = b 0 <;>
      simp [h, generatorWord_zero, contraction_monomial, one_def]
  | succ n ih =>
    rw [generatorWord_succ]
    change contraction GeneratorOrder.code a
      (wedge GeneratorOrder.code (generator (b 0)) (generatorWord (Fin.tail b))) = _
    rw [contraction_generator_wedge GeneratorOrder.code GeneratorOrder.code_injective, ih]
    change (if a = b 0 then generatorWord (Fin.tail b) else 0) -
      generator (b 0) * (∑ j : Fin (n + 1), (-1 : ℂ) ^ (j : ℕ) •
        (if a = Fin.tail b j then generatorWord (j.removeNth (Fin.tail b)) else 0)) = _
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_smul, generatorWord_remove_zero,
      mul_sum, sub_eq_add_neg, ← sum_neg_distrib]
    congr 1
    apply sum_congr rfl
    intro j _hj
    rw [generatorWord_remove_succ]
    by_cases h : a = b j.succ <;>
      simp [h, Fin.tail_def, pow_succ, mul_smul_comm]

/-- The coefficient pairing of ordered exterior words is the determinant of
the degree-one coefficient pairings. -/
theorem coefficientPairing_generatorWord {n : ℕ} (a b : Fin n → α) :
    coefficientPairing (generatorWord a) (generatorWord b) =
      Matrix.det (fun i j => if a i = b j then (1 : ℂ) else 0) := by
  induction n with
  | zero =>
    simp only [generatorWord_zero, Matrix.det_fin_zero]
    change coefficientPairing (monomial ∅) (monomial ∅) = 1
    simp [monomial]
  | succ n ih =>
    rw [generatorWord_succ, coefficientPairing_generator_mul, contraction_generatorWord,
      map_sum, Matrix.det_succ_row_zero]
    apply sum_congr rfl
    intro j _hj
    rw [map_smul]
    by_cases h : a 0 = b j
    · simp only [h, ite_eq_left, mul_one]
      rw [ih]
      rfl
    · simp [h]

end KhanSL2.FiniteExterior
