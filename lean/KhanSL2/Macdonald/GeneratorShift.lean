module

public import KhanSL2.Macdonald.Generators
public import KhanSL2.Macdonald.CoefficientShift
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! Exact coefficient-lowering formulas for the explicit Macdonald generators.
These are identities in the concrete mixed algebra, independent of cohomology. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

private theorem shifted_sigma_convolution (m n : ℕ) (a : Fin 3) :
    (∑ i ∈ Finset.range (n + 1), coefficientShift m (sigma a i) * sigma a (n - i)) =
      if m ≤ n then ∑ i ∈ Finset.range (n - m + 1),
        sigma a i * sigma a (n - m - i) else 0 := by
  by_cases hmn : m ≤ n
  · rw [if_pos hmn, show n + 1 = m + (n - m + 1) by omega,
      Finset.sum_range_add]
    have hz : (∑ i ∈ Finset.range m,
        coefficientShift m (sigma a i) * sigma a (n - i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hmi : ¬m ≤ i := by simpa using hi
      simp [coefficientShift_sigma, hmi]
    rw [hz, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coefficientShift_sigma, if_pos (by omega : m ≤ m + i)]
    simp only [show m + i - m = i by omega,
      show n - (m + i) = n - m - i by omega]
  · rw [if_neg hmn]
    apply Finset.sum_eq_zero
    intro i hi
    have hmi : ¬m ≤ i := by simp only [Finset.mem_range] at hi; omega
    simp [coefficientShift_sigma, hmi]

private theorem sigma_convolution_reflect (m n : ℕ) (a : Fin 3) :
    (∑ i ∈ Finset.range (n + 1), sigma a i * coefficientShift m (sigma a (n - i))) =
      ∑ i ∈ Finset.range (n + 1), coefficientShift m (sigma a i) * sigma a (n - i) := by
  rw [← Finset.sum_range_reflect
    (fun i => sigma a i * coefficientShift m (sigma a (n - i))) (n + 1)]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by simp only [Finset.mem_range] at hi; omega
  simp only [Nat.add_sub_cancel, show n - (n - i) = i by omega]
  exact sigma_commute a (n - i) _

/-- The even quadratic generator has coefficient multiplicity two. -/
theorem coefficientShift_S (m n : ℕ) :
    coefficientShift m (S n) = if m ≤ n then (2 : ℂ) • S (n - m) else 0 := by
  simp only [S, map_sum, coefficientShift_mul, Finset.sum_add_distrib]
  simp_rw [sigma_convolution_reflect, shifted_sigma_convolution]
  by_cases hmn : m ≤ n
  · simp only [if_pos hmn, two_smul, Finset.sum_add_distrib]
  · simp [hmn]

private theorem shifted_E_color (m n : ℕ) (a : Fin 3) :
    (∑ i ∈ Finset.range n, ((i + 1 : ℕ) : ℂ) •
      (coefficientShift m (sigma a (n - 1 - i)) * psi a i)) =
    ∑ i ∈ Finset.range (n - m), ((i + 1 : ℕ) : ℂ) •
      (sigma a (n - m - 1 - i) * psi a i) := by
  by_cases hmn : m ≤ n
  · calc
      _ = (∑ i ∈ Finset.range (n - m), ((i + 1 : ℕ) : ℂ) •
          (coefficientShift m (sigma a (n - 1 - i)) * psi a i)) +
          ∑ i ∈ Finset.range m, ((n - m + i + 1 : ℕ) : ℂ) •
            (coefficientShift m (sigma a (n - 1 - (n - m + i))) *
              psi a (n - m + i)) := by
        simpa only [Nat.sub_add_cancel hmn] using
          Finset.sum_range_add (fun i => ((i + 1 : ℕ) : ℂ) •
            (coefficientShift m (sigma a (n - 1 - i)) * psi a i)) (n - m) m
      _ = _ := by
        have hp : (∑ i ∈ Finset.range (n - m), ((i + 1 : ℕ) : ℂ) •
            (coefficientShift m (sigma a (n - 1 - i)) * psi a i)) =
            ∑ i ∈ Finset.range (n - m), ((i + 1 : ℕ) : ℂ) •
              (sigma a (n - m - 1 - i) * psi a i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi' : i < n - m := Finset.mem_range.mp hi
          rw [coefficientShift_sigma, if_pos (by omega : m ≤ n - 1 - i)]
          rw [show n - 1 - i - m = n - m - 1 - i by omega]
        have hz : (∑ i ∈ Finset.range m, ((n - m + i + 1 : ℕ) : ℂ) •
            (coefficientShift m (sigma a (n - 1 - (n - m + i))) *
              psi a (n - m + i))) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hi' : i < m := Finset.mem_range.mp hi
          have hm : ¬m ≤ n - 1 - (n - m + i) := by omega
          simp [coefficientShift_sigma, hm]
        rw [hp, hz, add_zero]
  · have hnm : n - m = 0 := by omega
    rw [hnm, Finset.range_zero, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro i hi
    have hm : ¬m ≤ n - 1 - i := by omega
    simp [coefficientShift_sigma, hm]

/-- The odd generator has coefficient multiplicity one, including the lower boundary. -/
theorem coefficientShift_E (m n : ℕ) :
    coefficientShift m (E n) = E (n - m) := by
  simp only [E, map_sum, map_smul, coefficientShift_mul,
    coefficientShift_psi, mul_zero, add_zero]
  exact Finset.sum_congr rfl fun a _ => shifted_E_color m n a

@[simp] theorem coefficientShift_S_self (n : ℕ) :
    coefficientShift n (S n) = (2 : ℂ) • S 0 := by
  simp [coefficientShift_S]

@[simp] theorem coefficientShift_E_self (n : ℕ) :
    coefficientShift n (E n) = 0 := by simp [coefficientShift_E]

theorem coefficientShift_S_eq_zero {m n : ℕ} (h : n < m) :
    coefficientShift m (S n) = 0 := by simp [coefficientShift_S, Nat.not_le.mpr h]

theorem coefficientShift_E_eq_zero {m n : ℕ} (h : n ≤ m) :
    coefficientShift m (E n) = 0 := by simp [coefficientShift_E, Nat.sub_eq_zero_of_le h]

end KhanSL2.Macdonald

