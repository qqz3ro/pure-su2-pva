module

public import KhanSL2.Injectivity.TaylorDiagonals
public import KhanSL2.Injectivity.DiagonalFactors

@[expose] public section

/-! The manuscript's discriminant divides every source-functional Taylor polynomial. -/

noncomputable section

namespace KhanSL2.SourceDual

open Source Injectivity

theorem discriminantFactor_dvd_taylorPolynomial (r s N : ℕ)
    (ell : Source →ₗ[ℂ] ℂ) :
    discriminantFactor r s ∣ taylorPolynomial r s N ell := by
  apply discriminantFactor_dvd_of_diagonals
  · intro i j hij
    exact ⟨taylorPolynomial_diagonal_x_eq_zero ell hij, taylorPolynomial_swap_x ell i j⟩
  · intro i j hij
    exact ⟨taylorPolynomial_swap_y ell hij, taylorPolynomial_diagonal_pderiv_y_eq_zero ell hij⟩
  · intro i j
    exact ⟨taylorPolynomial_diagonal_xy_eq_zero ell i j,
      taylorPolynomial_diagonal_pderiv_xy_eq_zero ell i j⟩

theorem exists_discriminant_quotient (r s N : ℕ) (ell : Source →ₗ[ℂ] ℂ) :
    ∃ q : MvPolynomial (Variables r s) ℂ,
      taylorPolynomial r s N ell = discriminantFactor r s * q :=
  discriminantFactor_dvd_taylorPolynomial r s N ell

end KhanSL2.SourceDual
