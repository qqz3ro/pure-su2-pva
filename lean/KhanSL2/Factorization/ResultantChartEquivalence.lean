module

public import KhanSL2.Factorization.ResultantChartTensorEquiv

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial TensorProduct
namespace KhanSL2.Factorization.ChartBridge

def productChartInclusion (r s : ℕ) : ProductCoefficients r s →ₐ[ℂ] ProductChart r s :=
  IsScalarTower.toAlgHom ℂ (ProductCoefficients r s) (ProductChart r s)

theorem firstOnProductChart_eq_map (r s : ℕ) :
    (firstOnProductChart r s).val = (Collision.univPoly r).map
      ((productChartInclusion r s).comp (leftCoefficients r s)).toRingHom := by
  change ((Collision.univPoly r).map (leftCoefficients r s).toRingHom).map _ = _
  rw [Polynomial.map_map]
  rfl

theorem secondOnProductChart_eq_map (r s : ℕ) :
    (secondOnProductChart r s).val = (Collision.univPoly s).map
      ((productChartInclusion r s).comp (rightCoefficients r s)).toRingHom := by
  change ((Collision.univPoly s).map (rightCoefficients r s).toRingHom).map _ = _
  rw [Polynomial.map_map]
  rfl

theorem productEvaluation_onChart (r s : ℕ) :
    productEvaluation (firstOnProductChart r s) (secondOnProductChart r s) =
      productChartInclusion r s := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro x
    change productEvaluation (firstOnProductChart r s) (secondOnProductChart r s)
      (leftCoefficients r s x) = productChartInclusion r s (leftCoefficients r s x)
    rw [productEvaluation_left,firstOnProductChart_eq_map]
    exact AlgHom.congr_fun (coeffHom_univPoly_map
      ((productChartInclusion r s).comp (leftCoefficients r s))) x
  · apply AlgHom.ext
    intro x
    change productEvaluation (firstOnProductChart r s) (secondOnProductChart r s)
      (rightCoefficients r s x) = productChartInclusion r s (rightCoefficients r s x)
    rw [productEvaluation_right,secondOnProductChart_eq_map]
    exact AlgHom.congr_fun (coeffHom_univPoly_map
      ((productChartInclusion r s).comp (rightCoefficients r s))) x

theorem universalToProductChart_comp_raw (r s : ℕ) :
    ((universalToProductChart r s).restrictScalars ℂ).comp (productToUniversalRaw r s) =
      productChartInclusion r s := by
  change ((universalToProductChart r s).restrictScalars ℂ).comp
    (productEvaluation (universalFirst r s) (universalSecond r s)) = _
  rw [← productEvaluation_map]
  have h₁ : (universalFirst r s).map
      ((universalToProductChart r s).restrictScalars ℂ).toRingHom = firstOnProductChart r s :=
    Subtype.ext (universalToProductChart_first r s)
  have h₂ : (universalSecond r s).map
      ((universalToProductChart r s).restrictScalars ℂ).toRingHom = secondOnProductChart r s :=
    Subtype.ext (universalToProductChart_second r s)
  rw [h₁,h₂,productEvaluation_onChart]

theorem universalToProductChart_comp (r s : ℕ) :
    (universalToProductChart r s).comp (productChartToUniversal r s) =
      AlgHom.id (Depth.RB (r+s)) (ProductChart r s) := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (productResultant r s))
  apply RingHom.ext
  intro a
  change universalToProductChart r s
      (productChartToUniversal r s (algebraMap (ProductCoefficients r s) (ProductChart r s) a)) =
    algebraMap (ProductCoefficients r s) (ProductChart r s) a
  rw [productChartToUniversal_algebraMap]
  exact AlgHom.congr_fun (universalToProductChart_comp_raw r s) a

/-- The universal coprime ring is exactly the ordinary product coefficient ring
localized at the resultant, preserving the original R_(r+s) action. -/
def universalProductChartEquiv (r s : ℕ) :
    Universal (r+s) r s rfl ≃ₐ[Depth.RB (r+s)] ProductChart r s :=
  AlgEquiv.ofAlgHom (universalToProductChart r s) (productChartToUniversal r s)
    (universalToProductChart_comp r s) (productChartToUniversal_comp r s)

instance productChart_etale (r s : ℕ) : Algebra.Etale (Depth.RB (r+s)) (ProductChart r s) :=
  Algebra.Etale.of_equiv (universalProductChartEquiv r s)

instance productChart_flat (r s : ℕ) : Module.Flat (Depth.RB (r+s)) (ProductChart r s) :=
  inferInstance

end KhanSL2.Factorization.ChartBridge
