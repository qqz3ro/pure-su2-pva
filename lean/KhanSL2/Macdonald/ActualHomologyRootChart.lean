module

public import KhanSL2.Macdonald.FixedRootChartBlockComparison

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel
open scoped WeightedFactorScalars FactorHomologyScalars

variable {s₁ s₂ : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
variable [Algebra (Depth.RB (s₁+s₂)) A] [IsScalarTower ℂ (Depth.RB (s₁+s₂)) A]
variable (c : Collision.ChartData (s₁+s₂) s₁ s₂ A)

/-- The actual normalized homology coproduct, after the two original factor insertions,
coincides with literal normalized root-chart restriction. -/
theorem specializedNormalizedHomologyCoproduct_chart
    (h : TotalHomology (symmetricPower (s₁+s₂))) :
    specializedNormalizedHomologyCoproduct s₁ s₂ c.f₁ c.f₂ h =
      normalizedHomologyRootChartEquiv c (1 ⊗ₜ[Depth.RB (s₁+s₂)] h) := by
  apply (factorSymmetricHomologyTensorRootEquiv s₁ s₂ c.f₁ c.f₂).injective
  apply DFinsupp.ext
  intro d
  exact (normalizedHomologyRootChartEquiv_unit_component c h d).symm

/-- Every coefficient-linear scalar extension of the specified normalized coproduct is the
proved literal chart equivalence. This identifies an independently constructed homology map. -/
theorem normalizedHomologyChart_eq_of_unit
    (F : (A ⊗[Depth.RB (s₁+s₂)] TotalHomology (symmetricPower (s₁+s₂))) →ₗ[A]
      FactorSymmetricHomology s₁ c.f₁ ⊗[A] FactorSymmetricHomology s₂ c.f₂)
    (hF : ∀ h, F (1 ⊗ₜ[Depth.RB (s₁+s₂)] h) =
      specializedNormalizedHomologyCoproduct s₁ s₂ c.f₁ c.f₂ h) :
    F = (normalizedHomologyRootChartEquiv c).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact F.map_zero.trans (normalizedHomologyRootChartEquiv c).map_zero.symm
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a h =>
    have he : a ⊗ₜ[Depth.RB (s₁+s₂)] h = a • (1 ⊗ₜ[Depth.RB (s₁+s₂)] h) := by
      simp only [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rw [he,map_smul,map_smul,hF,specializedNormalizedHomologyCoproduct_chart]
    rfl

/-- Bijectivity concerns the original map whenever its canonical unit-tensor formula is verified. -/
theorem normalizedHomologyChart_bijective_of_unit
    (F : (A ⊗[Depth.RB (s₁+s₂)] TotalHomology (symmetricPower (s₁+s₂))) →ₗ[A]
      FactorSymmetricHomology s₁ c.f₁ ⊗[A] FactorSymmetricHomology s₂ c.f₂)
    (hF : ∀ h, F (1 ⊗ₜ[Depth.RB (s₁+s₂)] h) =
      specializedNormalizedHomologyCoproduct s₁ s₂ c.f₁ c.f₂ h) : Function.Bijective F := by
  rw [normalizedHomologyChart_eq_of_unit c F hF]
  exact (normalizedHomologyRootChartEquiv c).bijective

end KhanSL2.Macdonald
