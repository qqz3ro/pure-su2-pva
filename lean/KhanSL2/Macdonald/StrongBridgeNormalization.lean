module

public import KhanSL2.Macdonald.StrongBridgeTotalCoordinates

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Explicit factorial normalization of the restricted-dual free coordinates. -/
noncomputable section
namespace KhanSL2.Macdonald

/-- Multiply each finite coordinate by its specified nonzero scalar. -/
def coordinateScale {ι : Type*} (c : ι → ℂ) : (ι →₀ ℂ) →ₗ[ℂ] (ι →₀ ℂ) where
  toFun u := Finsupp.onFinset u.support (fun i => c i * u i) (by
    intro i hi
    exact Finsupp.mem_support_iff.mpr (fun h => hi (by rw [h,mul_zero])))
  map_add' u v := by ext i; simp [mul_add]
  map_smul' a u := by ext i; simp [mul_left_comm]

@[simp] theorem coordinateScale_apply {ι : Type*} (c : ι → ℂ) (u : ι →₀ ℂ) (i : ι) :
    coordinateScale c u i = c i * u i := rfl

/-- Inverting the specified nonzero scalars gives the inverse normalization. -/
def coordinateScaleEquiv {ι : Type*} (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) :
    (ι →₀ ℂ) ≃ₗ[ℂ] (ι →₀ ℂ) where
  __ := coordinateScale c
  invFun := coordinateScale (fun i => (c i)⁻¹)
  left_inv u := by ext i; simp [← mul_assoc,hc]
  right_inv u := by ext i; simp [← mul_assoc,hc]

@[simp] theorem coordinateScaleEquiv_apply {ι : Type*} (c : ι → ℂ)
    (hc : ∀ i, c i ≠ 0) (u : ι →₀ ℂ) (i : ι) :
    coordinateScaleEquiv c hc u i = c i * u i := rfl

/-- Factorial weight of the actual color-zero symmetric monomial. -/
def strongFreeFactorial (b : strongFreeIndices) : ℂ :=
  exponentFactorial (strongExponentEquiv b.val.1)

theorem strongFreeFactorial_ne_zero (b : strongFreeIndices) : strongFreeFactorial b ≠ 0 :=
  Nat.cast_ne_zero.mpr (exponentFactorial_ne_zero _)

/-- Convert evaluation coordinates into ordinary symmetric monomial coefficients. -/
def strongFreeNormalization : (strongFreeIndices →₀ ℂ) ≃ₗ[ℂ] (strongFreeIndices →₀ ℂ) :=
  coordinateScaleEquiv (fun b => (strongFreeFactorial b)⁻¹)
    (fun b => inv_ne_zero (strongFreeFactorial_ne_zero b))

/-- The explicit normalized free model of actual symmetric relative homology. -/
def strongTotalHomologyFreeEquiv :
    Factorization.TotalHomology SymmetricCoefficients ≃ₗ[ℂ] strongFree :=
  strongTotalHomologyCoordinateEquiv.trans
    (strongFreeNormalization.trans strongFreeCoordinateEquiv.symm)

@[simp] theorem strongTotalHomologyFreeEquiv_coordinate
    (u : Factorization.TotalHomology SymmetricCoefficients) (b : strongFreeIndices) :
    strongFreeCoordinateEquiv (strongTotalHomologyFreeEquiv u) b =
      (strongFreeFactorial b)⁻¹ * strongTotalHomologyCoordinateEquiv u b := by
  simp [strongTotalHomologyFreeEquiv,strongFreeNormalization]

end KhanSL2.Macdonald
