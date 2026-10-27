module

public import KhanSL2.Macdonald.Basic

@[expose] public section

/-! The explicit quadratic and odd generators of the restricted Macdonald model.
The exterior index `i` represents physical mode `i + 1`. All sums are finite. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

/-- The quadratic coefficient of the invariant symmetric generating series. -/
def S (n : ℕ) : W :=
  ∑ a : Fin 3, ∑ i ∈ Finset.range (n + 1), sigma a i * sigma a (n - i)

/-- The odd coefficient, with the derivative factor from its positive exterior mode. -/
def E (n : ℕ) : W :=
  ∑ a : Fin 3, ∑ i ∈ Finset.range n,
    ((i + 1 : ℕ) : ℂ) • (sigma a (n - 1 - i) * psi a i)

theorem S_zero : S 0 = ∑ a : Fin 3, sigma a 0 * sigma a 0 := by
  simp [S]

@[simp] theorem E_zero : E 0 = 0 := by simp [E]

theorem E_succ (n : ℕ) :
    E (n + 1) = ∑ a : Fin 3, ∑ i ∈ Finset.range (n + 1),
      ((i + 1 : ℕ) : ℂ) • (sigma a (n - i) * psi a i) := by
  simp [E]

theorem E_one : E 1 = ∑ a : Fin 3, sigma a 0 * psi a 0 := by
  simp [E]

end KhanSL2.Macdonald
