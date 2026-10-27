module

public import KhanSL2.Macdonald.FinitePieces
public import KhanSL2.Macdonald.GeneratorDegrees
public import KhanSL2.Macdonald.GeneratorShift

@[expose] public section

/-!
# First milestone toward the strong Macdonald calculation

`W` is the concrete tensor product of the polynomial algebra on nonnegative
even modes and the exterior algebra on positive odd modes. Its pieces are
indexed by weight, symmetric degree, and exterior degree, in that order.
Fixing the symmetric degree is essential: the even zero modes have weight zero.

The theorem below packages finite-dimensionality of these pieces, the degrees
of the explicit candidate generators `S` and `E`, and the action on them of
the coefficient-lowering operator. The latter satisfies the Leibniz rule on
the entire mixed algebra. Natural-number subtraction in the `E` formula is
compatible with the lower boundary because `E 0 = 0`.

This milestone does not construct a CE differential, prove that `S` and `E`
are relative cocycles, or identify a cohomology algebra. In particular, it is
not a proof or an assumed instance of the strong Macdonald theorem.
-/

noncomputable section

namespace KhanSL2.Macdonald

/-- The concrete algebra, grading, and coefficient-shift milestone. -/
theorem milestoneGenerators :
    (∀ w s k : ℕ, FiniteDimensional ℂ (piece w s k)) ∧
    (∀ w s : ℕ, FiniteDimensional ℂ (weightDegreePiece w s)) ∧
    (∀ w s k : ℕ, w < k → piece w s k = ⊥) ∧
    (∀ n : ℕ, S n ∈ piece n 2 0) ∧
    (∀ n : ℕ, E n ∈ piece n 1 1) ∧
    (∀ (m : ℕ) (u v : W),
      coefficientShift m (u * v) = coefficientShift m u * v + u * coefficientShift m v) ∧
    (∀ m n : ℕ, coefficientShift m (S n) =
      if m ≤ n then (2 : ℂ) • S (n - m) else 0) ∧
    (∀ m n : ℕ, coefficientShift m (E n) = E (n - m)) ∧
    E 0 = 0 :=
  ⟨fun _ _ _ => inferInstance, fun _ _ => inferInstance,
    fun _ _ _ h => piece_eq_bot_of_weight_lt_degree h,
    S_mem_piece, E_mem_piece, coefficientShift_mul,
    coefficientShift_S, coefficientShift_E, E_zero⟩

end KhanSL2.Macdonald
