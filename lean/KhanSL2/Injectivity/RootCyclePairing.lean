module

public import KhanSL2.Injectivity.RootCycles
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Determinantal pairing of the explicit Cartan cycles -/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity

open Finset

variable {σ ι R : Type*} [Fintype σ] [Fintype ι] [DecidableEq ι]
  [CommRing R] [Algebra ℚ R]

/-- The Cartan determinant gives exactly the cross-diagonal factor times
the exponent alternant, with one minus sign for each Cartan cycle. -/
theorem rootCycle_pairing_det (w : σ → R) (z : ι → R) (n : ι → ℕ) :
    Matrix.det (fun i j =>
      cartanModePairing (z i) (rootCycle w w (Fintype.card σ + 1 + n j))) =
      (∏ i, -(∏ a, (z i - w a))) * Matrix.det (fun i j => z i ^ n j) := by
  have hmatrix :
      (fun i j => cartanModePairing (z i)
        (rootCycle w w (Fintype.card σ + 1 + n j))) =
      (fun i j => -(∏ a, (z i - w a)) * z i ^ n j) := by
    funext i j
    rw [rootCycle_pairing]
    ring
  rw [hmatrix]
  exact Matrix.det_mul_column _ _

end KhanSL2.Injectivity
