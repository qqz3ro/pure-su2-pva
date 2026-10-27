module

public import KhanSL2.Factorization.ResultantChartFactorFlat

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Every etale coprime chart is flat over the two independent coefficient
rings taken together. This is the external-variable flatness needed for
Künneth; no general tensor-of-homology assertion over the chart is assumed. -/
noncomputable section
namespace KhanSL2.Factorization.ChartBridge
variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]

/-- The joint original factor-coefficient action, through the actual resultant chart. -/
abbrev chartProductAlgebra (c : Collision.ChartData (r+s) r s A) :
    Algebra (ProductCoefficients r s) A :=
  ((productChartSpecialization c).toRingHom.comp
    (algebraMap (ProductCoefficients r s) (ProductChart r s))).toAlgebra

/-- The joint coefficient action and chart action form the literal scalar tower. -/
theorem chartProduct_tower (c : Collision.ChartData (r+s) r s A) :
    let := productChartSpecializationAlgebra c
    let := chartProductAlgebra c
    IsScalarTower (ProductCoefficients r s) (ProductChart r s) A := by
  let := productChartSpecializationAlgebra c
  let := chartProductAlgebra c
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Simultaneous flatness over the independent factor variables. -/
theorem chart_flat_product [Algebra.Etale (Depth.RB (r+s)) A]
    (c : Collision.ChartData (r+s) r s A) :
    let := chartProductAlgebra c
    Module.Flat (ProductCoefficients r s) A := by
  let := productChartSpecializationAlgebra c
  let := chartProductAlgebra c
  let := chartProduct_tower c
  let := productChartSpecialization_flat c
  exact Module.Flat.trans (ProductCoefficients r s) (ProductChart r s) A

variable [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- The joint action restricts to the first originally prescribed factor action. -/
theorem chartProduct_left (c : Collision.ChartData (r+s) r s A) (x : Depth.RB r) :
    let := chartProductAlgebra c
    algebraMap (ProductCoefficients r s) A (leftCoefficients r s x) =
      Collision.coeffHom r c.f₁ x := by
  exact (AlgHom.congr_fun (productChartSpecialization_left c) x).symm

/-- Its restriction to the other factor is also the original coefficient map. -/
theorem chartProduct_right (c : Collision.ChartData (r+s) r s A) (x : Depth.RB s) :
    let := chartProductAlgebra c
    algebraMap (ProductCoefficients r s) A (rightCoefficients r s x) =
      Collision.coeffHom s c.f₂ x := by
  exact (AlgHom.congr_fun (productChartSpecialization_right c) x).symm

end KhanSL2.Factorization.ChartBridge
