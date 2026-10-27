module

public import KhanSL2.Macdonald.StrongBridgeFixedRootProjection

@[expose] public section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-! The actual fixed symmetric homology coproduct has the same root components
as the full coproduct, after the already verified original degree projection. -/
noncomputable section
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open Factorization

/-- Exact root-component formula for the original fixed-degree homology coproduct. -/
theorem symmetricPowerHomologyCoproduct_rootComponent (s₁ s₂ : ℕ)
    (d₁ : RootHomologyDegrees s₁) (d₂ : RootHomologyDegrees s₂)
    (h : TotalHomology (symmetricPower (s₁+s₂))) :
    TensorProduct.map (fixedRootHomologyComponent s₁ d₁) (fixedRootHomologyComponent s₂ d₂)
      (symmetricPowerHomologyCoproduct s₁ s₂ h) =
      TensorProduct.map (totalRootHomologyComponent d₁.val) (totalRootHomologyComponent d₂.val)
        (symmetricHomologyCoproduct (symmetricHomologyInclusion (s₁+s₂) h)) := by
  have h₁ : (fixedRootHomologyComponent s₁ d₁).comp (symmetricHomologyProjection s₁) =
      totalRootHomologyComponent d₁.val :=
    LinearMap.ext (fixedRootHomologyComponent_projection s₁ d₁)
  have h₂ : (fixedRootHomologyComponent s₂ d₂).comp (symmetricHomologyProjection s₂) =
      totalRootHomologyComponent d₂.val :=
    LinearMap.ext (fixedRootHomologyComponent_projection s₂ d₂)
  rw [symmetricPowerHomologyCoproduct_eq_projection]
  change ((TensorProduct.map (fixedRootHomologyComponent s₁ d₁) (fixedRootHomologyComponent s₂ d₂)).comp
    (TensorProduct.map (symmetricHomologyProjection s₁) (symmetricHomologyProjection s₂)))
      (symmetricHomologyCoproduct (symmetricHomologyInclusion (s₁+s₂) h)) = _
  rw [← TensorProduct.map_comp,h₁,h₂]

end KhanSL2.Macdonald
