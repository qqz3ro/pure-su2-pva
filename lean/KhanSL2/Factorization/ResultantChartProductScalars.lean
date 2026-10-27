module

public import KhanSL2.Factorization.ResultantChartProductFlat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.ChartBridge
variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- Joint chart scalars multiply the two original signed coefficient images. -/
theorem chartProduct_tmul (c : Collision.ChartData (r+s) r s A)
    (x : Depth.RB r) (y : Depth.RB s) :
    let := chartProductAlgebra c
    algebraMap (ProductCoefficients r s) A (x ⊗ₜ[ℂ] y) =
      Collision.coeffHom r c.f₁ x * Collision.coeffHom s c.f₂ y := by
  let := chartProductAlgebra c
  have h : (x ⊗ₜ[ℂ] y : ProductCoefficients r s) =
      leftCoefficients r s x * rightCoefficients r s y := by
    change x ⊗ₜ[ℂ] y = (x ⊗ₜ[ℂ] 1) * (1 ⊗ₜ[ℂ] y)
    simp only [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  change algebraMap (ProductCoefficients r s) A (x ⊗ₜ[ℂ] y) = _
  rw [h,map_mul,chartProduct_left,chartProduct_right]

/-- The joint action also retains the given complex scalar structure. -/
theorem chartProduct_complexTower (c : Collision.ChartData (r+s) r s A) :
    let := chartProductAlgebra c
    IsScalarTower ℂ (ProductCoefficients r s) A := by
  let := chartProductAlgebra c
  apply IsScalarTower.of_algebraMap_eq
  intro z
  rw [← (leftCoefficients r s).commutes z,chartProduct_left]
  exact ((Collision.coeffHom r c.f₁).commutes z).symm

end KhanSL2.Factorization.ChartBridge
