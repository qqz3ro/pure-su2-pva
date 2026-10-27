module

public import KhanSL2.Macdonald.Grading
public import KhanSL2.Macdonald.Generators

@[expose] public section

/-! The degrees of the explicit even and odd candidate generators. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

/-- The quadratic coefficient has weight n, symmetric degree two, and exterior degree zero. -/
theorem S_mem_piece (n : ℕ) : S n ∈ piece n 2 0 := by
  unfold S
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro i hi
  have hin : i < n + 1 := Finset.mem_range.mp hi
  have hw : i + (n - i) = n := by omega
  simpa only [hw] using mul_mem_piece (sigma_mem_piece a i) (sigma_mem_piece a (n-i))

/-- The odd coefficient has weight n and one factor of each kind, including E 0 = 0. -/
theorem E_mem_piece (n : ℕ) : E n ∈ piece n 1 1 := by
  unfold E
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  have hin : i < n := Finset.mem_range.mp hi
  have hw : n - 1 - i + (i + 1) = n := by omega
  simpa only [hw, Nat.add_zero, Nat.zero_add] using
    mul_mem_piece (sigma_mem_piece a (n-1-i)) (psi_mem_piece a i)

end KhanSL2.Macdonald
