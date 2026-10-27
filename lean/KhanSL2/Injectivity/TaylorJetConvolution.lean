module

public import KhanSL2.Injectivity.TaylorRelations

@[expose] public section

/-! Explicit factorial-normalized jet identities, with arbitrary residual monomials. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.Source

theorem factorial_convolution_eq_zero (ell : Source →ₗ[ℂ] ℂ) (n : ℕ)
    (right : Source) (C : ℂ) {a b : Source} (h : a * b = 0) :
    (∑ ij ∈ Finset.antidiagonal n,
      ell (((translation ^ ij.1) a * (translation ^ ij.2) b) * right) /
        ((Nat.factorial ij.1 : ℂ) * (Nat.factorial ij.2 : ℂ) * C)) = 0 := by
  have hz := functional_convolution_eq_zero ell n 1 right h
  simp only [one_mul] at hz
  calc
    _ = C⁻¹ * ∑ ij ∈ Finset.antidiagonal n,
      ell ((dividedTranslate ij.1 a * dividedTranslate ij.2 b) * right) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ij _ => ?_
        simp only [dividedTranslate, smul_mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul,
          map_smul, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
        ring
    _ = 0 := by rw [hz, mul_zero]

theorem factorial_convolution_XX (ell : Source →ₗ[ℂ] ℂ) (n : ℕ)
    (right : Source) (C : ℂ) :
    (∑ ij ∈ Finset.antidiagonal n,
      ell ((X ij.1 * X ij.2) * right) /
        ((Nat.factorial ij.1 : ℂ) * (Nat.factorial ij.2 : ℂ) * C)) = 0 := by
  simpa using factorial_convolution_eq_zero ell n right C X0_sq

theorem factorial_convolution_XY (ell : Source →ₗ[ℂ] ℂ) (n : ℕ)
    (right : Source) (C : ℂ) :
    (∑ ij ∈ Finset.antidiagonal n,
      ell ((X ij.1 * Y ij.2) * right) /
        ((Nat.factorial ij.1 : ℂ) * (Nat.factorial ij.2 : ℂ) * C)) = 0 := by
  simpa using factorial_convolution_eq_zero ell n right C X0_Y0

theorem factorial_convolution_dXY (ell : Source →ₗ[ℂ] ℂ) (n : ℕ)
    (right : Source) (C : ℂ) :
    (∑ ij ∈ Finset.antidiagonal n,
      ell ((X (ij.1 + 1) * Y ij.2) * right) /
        ((Nat.factorial ij.1 : ℂ) * (Nat.factorial ij.2 : ℂ) * C)) = 0 := by
  simpa [Nat.add_comm] using factorial_convolution_eq_zero ell n right C X1_Y0

theorem factorial_convolution_dYY (ell : Source →ₗ[ℂ] ℂ) (n : ℕ)
    (right : Source) (C : ℂ) :
    (∑ ij ∈ Finset.antidiagonal n,
      ell ((Y (ij.1 + 1) * Y ij.2) * right) /
        ((Nat.factorial ij.1 : ℂ) * (Nat.factorial ij.2 : ℂ) * C)) = 0 := by
  simpa [Nat.add_comm] using factorial_convolution_eq_zero ell n right C Y1_Y0

end KhanSL2.Source
