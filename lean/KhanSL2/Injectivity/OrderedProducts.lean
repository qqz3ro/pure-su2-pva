module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace KhanSL2.Injectivity

open Finset

variable {A : Type*} [Ring A]

/-- Products in index order, without assuming the factors commute. -/
def orderedProduct {n : ℕ} (f : Fin n → A) : A := (List.ofFn f).prod

@[simp] theorem orderedProduct_zero (f : Fin 0 → A) : orderedProduct f = 1 := by
  simp [orderedProduct]

theorem orderedProduct_succ {n : ℕ} (f : Fin (n + 1) → A) :
    orderedProduct f = f 0 * orderedProduct (Fin.tail f) := by
  simp [orderedProduct, List.ofFn_succ, Fin.tail_def]

theorem orderedProduct_append {m n : ℕ} (a : Fin m → A) (b : Fin n → A) :
    orderedProduct (Fin.append a b) = orderedProduct a * orderedProduct b := by
  simp only [orderedProduct, List.ofFn_fin_append, List.prod_append]

theorem orderedProduct_update_zero {n : ℕ} (f : Fin (n + 1) → A) (a : A) :
    orderedProduct (Function.update f 0 a) = a * orderedProduct (Fin.tail f) := by
  rw [orderedProduct_succ, Function.update_self, Fin.tail_update_zero]

theorem orderedProduct_update_succ {n : ℕ} (f : Fin (n + 1) → A) (i : Fin n) (a : A) :
    orderedProduct (Function.update f i.succ a) =
      f 0 * orderedProduct (Function.update (Fin.tail f) i a) := by
  rw [orderedProduct_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm,
    Fin.tail_update_succ]

theorem orderedProduct_update_neg {n : ℕ} (f : Fin n → A) (i : Fin n) (a : A) :
    orderedProduct (Function.update f i (-a)) = -orderedProduct (Function.update f i a) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => rw [orderedProduct_update_zero, orderedProduct_update_zero, neg_mul]
    | succ i =>
      rw [orderedProduct_update_succ, orderedProduct_update_succ, ih, mul_neg]

variable {K : Type*} [CommRing K] [Algebra K A]

/-- The Leibniz expansion of an even derivation on an ordered product. -/
theorem linearMap_orderedProduct (D : A →ₗ[K] A)
    (hD : ∀ a b, D (a * b) = D a * b + a * D b) (h1 : D 1 = 0)
    {n : ℕ} (f : Fin n → A) :
    D (orderedProduct f) = ∑ i, orderedProduct (Function.update f i (D (f i))) := by
  induction n with
  | zero => simp [h1]
  | succ n ih =>
    rw [orderedProduct_succ, hD, ih, Fin.sum_univ_succ, orderedProduct_update_zero, mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _hi
    rw [orderedProduct_update_succ]
    rfl

end KhanSL2.Injectivity
