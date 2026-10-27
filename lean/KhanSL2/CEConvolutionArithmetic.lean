module

public import KhanSL2.CELeibniz

@[expose] public section

/-! Finite weighted convolution identities for normalized translation. -/

noncomputable section

namespace KhanSL2

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem weighted_sum_shift (j : ℕ) (A : ℕ → M) :
    (∑ i ∈ Finset.range j, ((i + 2 : ℕ) : ℂ) • A (i + 1)) =
      (∑ i ∈ Finset.range (j + 1), ((i + 1 : ℕ) : ℂ) • A i) - A 0 := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.cast_one, one_smul]
  abel

theorem weighted_sum_tail (j κ : ℕ) (A : ℕ → M) :
    (∑ i ∈ Finset.range j, ((j - i + κ : ℕ) : ℂ) • A i) =
      (∑ i ∈ Finset.range (j + 1), ((j - i + κ : ℕ) : ℂ) • A i) -
        (κ : ℂ) • A j := by
  rw [Finset.sum_range_succ]
  simp

theorem weighted_convolution_translation (j κ : ℕ) (A : ℕ → M) :
    (∑ i ∈ Finset.range j,
      (((i + 2 : ℕ) : ℂ) • A (i + 1) + ((j - i + κ : ℕ) : ℂ) • A i)) =
      ((j + κ + 1 : ℕ) : ℂ) • (∑ i ∈ Finset.range (j + 1), A i) -
        A 0 - (κ : ℂ) • A j := by
  rw [Finset.sum_add_distrib, weighted_sum_shift, weighted_sum_tail]
  have hsum :
      (∑ i ∈ Finset.range (j + 1), ((i + 1 : ℕ) : ℂ) • A i) +
        (∑ i ∈ Finset.range (j + 1), ((j - i + κ : ℕ) : ℂ) • A i) =
      ((j + κ + 1 : ℕ) : ℂ) • (∑ i ∈ Finset.range (j + 1), A i) := by
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← add_smul, ← Nat.cast_add]
    congr 2
    have hi' := Finset.mem_range.mp hi
    omega
  calc
    _ = ((∑ i ∈ Finset.range (j + 1), ((i + 1 : ℕ) : ℂ) • A i) +
        (∑ i ∈ Finset.range (j + 1), ((j - i + κ : ℕ) : ℂ) • A i)) -
        A 0 - (κ : ℂ) • A j := by abel
    _ = _ := by rw [hsum]

end KhanSL2
