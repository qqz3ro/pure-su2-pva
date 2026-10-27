module

public import KhanSL2.Factorization.ResultantChartEquivalence

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial TensorProduct
namespace KhanSL2.Factorization.ChartBridge

abbrev leftProductAlgebra (r s : ℕ) : Algebra (Depth.RB r) (ProductCoefficients r s) :=
  inferInstanceAs (Algebra (Depth.RB r) (Depth.RB r ⊗[ℂ] Depth.RB s))

abbrev rightProductAlgebra (r s : ℕ) : Algebra (Depth.RB s) (ProductCoefficients r s) :=
  Algebra.TensorProduct.rightAlgebra

theorem productCoefficients_flat_left (r s : ℕ) :
    let := leftProductAlgebra r s
    Module.Flat (Depth.RB r) (ProductCoefficients r s) := by
  let := leftProductAlgebra r s
  exact inferInstanceAs (Module.Flat (Depth.RB r) (Depth.RB r ⊗[ℂ] Depth.RB s))

theorem productCoefficients_flat_right (r s : ℕ) :
    let := rightProductAlgebra r s
    Module.Flat (Depth.RB s) (ProductCoefficients r s) := by
  let := rightProductAlgebra r s
  let : Algebra (Depth.RB s) (Depth.RB r ⊗[ℂ] Depth.RB s) := Algebra.TensorProduct.rightAlgebra
  exact Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight ℂ (Depth.RB s) (Depth.RB r)).symm.toLinearEquiv

abbrev leftChartAlgebra (r s : ℕ) : Algebra (Depth.RB r) (ProductChart r s) :=
  let := leftProductAlgebra r s
  inferInstance

abbrev rightChartAlgebra (r s : ℕ) : Algebra (Depth.RB s) (ProductChart r s) :=
  let := rightProductAlgebra r s
  inferInstance

theorem productChart_flat_left (r s : ℕ) :
    let := leftChartAlgebra r s
    Module.Flat (Depth.RB r) (ProductChart r s) := by
  let := leftProductAlgebra r s
  let := leftChartAlgebra r s
  let : IsScalarTower (Depth.RB r) (ProductCoefficients r s) (ProductChart r s) :=
    inferInstance
  let := productCoefficients_flat_left r s
  exact Module.Flat.trans (Depth.RB r) (ProductCoefficients r s) (ProductChart r s)

theorem productChart_flat_right (r s : ℕ) :
    let := rightChartAlgebra r s
    Module.Flat (Depth.RB s) (ProductChart r s) := by
  let := rightProductAlgebra r s
  let := rightChartAlgebra r s
  let : IsScalarTower (Depth.RB s) (ProductCoefficients r s) (ProductChart r s) :=
    inferInstance
  let := productCoefficients_flat_right r s
  exact Module.Flat.trans (Depth.RB s) (ProductCoefficients r s) (ProductChart r s)

section Specialization
variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]

/-- The map from the disjoint-factor chart to any specified coprime factorization. -/
def productChartSpecialization (c : Collision.ChartData (r+s) r s A) :
    ProductChart r s →ₐ[Depth.RB (r+s)] A :=
  (specialization rfl c).comp (universalProductChartEquiv r s).symm.toAlgHom

abbrev productChartSpecializationAlgebra (c : Collision.ChartData (r+s) r s A) :
    Algebra (ProductChart r s) A := (productChartSpecialization c).toRingHom.toAlgebra

theorem productChartSpecialization_tower (c : Collision.ChartData (r+s) r s A) :
    let := productChartSpecializationAlgebra c
    IsScalarTower (Depth.RB (r+s)) (ProductChart r s) A := by
  let := productChartSpecializationAlgebra c
  exact IsScalarTower.of_algebraMap_eq fun z => ((productChartSpecialization c).commutes z).symm

theorem productChartSpecialization_etale [Algebra.Etale (Depth.RB (r+s)) A]
    (c : Collision.ChartData (r+s) r s A) :
    let := productChartSpecializationAlgebra c
    Algebra.Etale (ProductChart r s) A := by
  let := productChartSpecializationAlgebra c
  let := productChartSpecialization_tower c
  exact Algebra.Etale.of_restrictScalars (Depth.RB (r+s)) (ProductChart r s) A

theorem productChartSpecialization_flat [Algebra.Etale (Depth.RB (r+s)) A]
    (c : Collision.ChartData (r+s) r s A) :
    let := productChartSpecializationAlgebra c
    Module.Flat (ProductChart r s) A := by
  let := productChartSpecializationAlgebra c
  let := productChartSpecialization_etale c
  infer_instance

end Specialization
end KhanSL2.Factorization.ChartBridge
