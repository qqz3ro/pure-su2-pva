module

public import KhanSL2.Factorization.ResultantChartFlat

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial TensorProduct
namespace KhanSL2.Factorization.ChartBridge

section Chart
variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]

theorem productChartSpecialization_first (c : Collision.ChartData (r+s) r s A) :
    (firstOnProductChart r s).val.map (productChartSpecialization c).toRingHom = c.f₁ := by
  change (firstOnProductChart r s).val.map
    ((specialization rfl c).toRingHom.comp (productChartToUniversal r s).toRingHom) = _
  rw [← Polynomial.map_map,productChartToUniversal_first]
  exact specialization_factor₁ rfl c

theorem productChartSpecialization_second (c : Collision.ChartData (r+s) r s A) :
    (secondOnProductChart r s).val.map (productChartSpecialization c).toRingHom = c.f₂ := by
  change (secondOnProductChart r s).val.map
    ((specialization rfl c).toRingHom.comp (productChartToUniversal r s).toRingHom) = _
  rw [← Polynomial.map_map,productChartToUniversal_second]
  exact specialization_factor₂ rfl c

variable [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

theorem productChartSpecialization_left (c : Collision.ChartData (r+s) r s A) :
    Collision.coeffHom r c.f₁ = ((productChartSpecialization c).restrictScalars ℂ).comp
      ((productChartInclusion r s).comp (leftCoefficients r s)) := by
  have h := coeffHom_map r (firstOnProductChart r s).val
    ((productChartSpecialization c).restrictScalars ℂ)
  change Collision.coeffHom r ((firstOnProductChart r s).val.map
    (productChartSpecialization c).toRingHom) = _ at h
  rw [productChartSpecialization_first,firstOnProductChart_eq_map,
    coeffHom_univPoly_map] at h
  exact h

theorem productChartSpecialization_right (c : Collision.ChartData (r+s) r s A) :
    Collision.coeffHom s c.f₂ = ((productChartSpecialization c).restrictScalars ℂ).comp
      ((productChartInclusion r s).comp (rightCoefficients r s)) := by
  have h := coeffHom_map s (secondOnProductChart r s).val
    ((productChartSpecialization c).restrictScalars ℂ)
  change Collision.coeffHom s ((secondOnProductChart r s).val.map
    (productChartSpecialization c).toRingHom) = _ at h
  rw [productChartSpecialization_second,secondOnProductChart_eq_map,
    coeffHom_univPoly_map] at h
  exact h

end Chart

section Flatness
variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]

/-- Flatness over the first factor uses exactly the signed elementary coefficient
map in `ChartData.algebra₁`, not an unspecified choice of scalar action. -/
theorem chart_flat_left [Algebra.Etale (Depth.RB (r+s)) A]
    (c : Collision.ChartData (r+s) r s A) :
    let := c.algebra₁
    Module.Flat (Depth.RB r) A := by
  let : Algebra ℂ A := Collision.chartComplexAlgebra (B := r+s)
  let : IsScalarTower ℂ (Depth.RB (r+s)) A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := c.algebra₁
  let := leftChartAlgebra r s
  let := productChartSpecializationAlgebra c
  let : IsScalarTower (Depth.RB r) (ProductChart r s) A :=
    IsScalarTower.of_algebraMap_eq fun z => AlgHom.congr_fun (productChartSpecialization_left c) z
  let := productChart_flat_left r s
  let := productChartSpecialization_flat c
  exact Module.Flat.trans (Depth.RB r) (ProductChart r s) A

/-- The analogous second-factor flatness, including arbitrary nonreduced charts. -/
theorem chart_flat_right [Algebra.Etale (Depth.RB (r+s)) A]
    (c : Collision.ChartData (r+s) r s A) :
    let := c.algebra₂
    Module.Flat (Depth.RB s) A := by
  let : Algebra ℂ A := Collision.chartComplexAlgebra (B := r+s)
  let : IsScalarTower ℂ (Depth.RB (r+s)) A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := c.algebra₂
  let := rightChartAlgebra r s
  let := productChartSpecializationAlgebra c
  let : IsScalarTower (Depth.RB s) (ProductChart r s) A :=
    IsScalarTower.of_algebraMap_eq fun z => AlgHom.congr_fun (productChartSpecialization_right c) z
  let := productChart_flat_right r s
  let := productChartSpecialization_flat c
  exact Module.Flat.trans (Depth.RB s) (ProductChart r s) A

end Flatness

/-- Every chart quantified by `KFactor` is flat over both smaller coefficient
rings, for the coefficient actions already fixed in that statement. -/
theorem chart_flat_factors {B r s : ℕ} (hsum : r+s=B)
    {A : Type} [CommRing A] [Algebra (Depth.RB B) A] [Algebra.Etale (Depth.RB B) A]
    (c : Collision.ChartData B r s A) :
    (let := c.algebra₁; Module.Flat (Depth.RB r) A) ∧
    (let := c.algebra₂; Module.Flat (Depth.RB s) A) := by
  subst B
  exact ⟨chart_flat_left c,chart_flat_right c⟩

end KhanSL2.Factorization.ChartBridge
