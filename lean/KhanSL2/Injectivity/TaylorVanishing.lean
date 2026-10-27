module

public import KhanSL2.Injectivity.TaylorSymmetry
public import KhanSL2.Injectivity.DiagonalDivisibility

@[expose] public section

/-! First diagonal consequences of the symmetry of source Taylor polynomials. -/

noncomputable section

namespace KhanSL2.SourceDual

open Source Injectivity MvPolynomial

@[simp] theorem xPermutation_swap {r s : ℕ} (i j : Fin r) :
    xPermutation (s := s) (Equiv.swap i j) = Equiv.swap (Sum.inl i) (Sum.inl j) := by
  ext k
  rcases k with k | k <;> simp [xPermutation, Equiv.swap_apply_def]

@[simp] theorem yPermutation_swap {r s : ℕ} (i j : Fin s) :
    yPermutation (r := r) (Equiv.swap i j) = Equiv.swap (Sum.inr i) (Sum.inr j) := by
  ext k
  rcases k with k | k <;> simp [yPermutation, Equiv.swap_apply_def]

theorem taylorPolynomial_swap_x {r s N : ℕ} (ell : Source →ₗ[ℂ] ℂ)
    (i j : Fin r) :
    rename (Equiv.swap (Sum.inl i) (Sum.inl j)) (taylorPolynomial r s N ell) =
      taylorPolynomial r s N ell := by
  simpa using taylorPolynomial_symmetric_x ell (Equiv.swap i j)

theorem taylorPolynomial_swap_y {r s N : ℕ} (ell : Source →ₗ[ℂ] ℂ)
    {i j : Fin s} (hij : i ≠ j) :
    rename (Equiv.swap (Sum.inr i) (Sum.inr j)) (taylorPolynomial r s N ell) =
      -taylorPolynomial r s N ell := by
  simpa [Equiv.Perm.sign_swap hij] using
    taylorPolynomial_alternating_y ell (Equiv.swap i j)

theorem taylorPolynomial_diagonal_y_eq_zero {r s N : ℕ} (ell : Source →ₗ[ℂ] ℂ)
    {i j : Fin s} (hij : i ≠ j) :
    diagonal (Sum.inr i) (Sum.inr j) (taylorPolynomial r s N ell) = 0 :=
  diagonal_eq_zero_of_antisymmetric _ _ _ (taylorPolynomial_swap_y ell hij)

theorem y_difference_dvd_taylorPolynomial {r s N : ℕ} (ell : Source →ₗ[ℂ] ℂ)
    {i j : Fin s} (hij : i ≠ j) :
    (MvPolynomial.X (Sum.inr i) - MvPolynomial.X (Sum.inr j) :
      MvPolynomial (Variables r s) ℂ) ∣
      taylorPolynomial r s N ell :=
  (diagonal_eq_zero_iff_dvd (Sum.inr_injective.ne hij) _).mp
    (taylorPolynomial_diagonal_y_eq_zero ell hij)

end KhanSL2.SourceDual
