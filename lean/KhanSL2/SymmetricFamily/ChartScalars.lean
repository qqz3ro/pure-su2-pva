module

public import KhanSL2.SymmetricFamily.SymmetricChartNormalization
public import KhanSL2.SymmetricFamily.ExteriorChartNormalization

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The chart current maps preserve the actual coefficient-algebra scalar
action, so they can be used directly by the coefficient-linear CE functor. -/
noncomputable section
namespace KhanSL2.SymmetricFamily
open Macdonald

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

theorem symmetricChartCurrentMap_smul (c : Collision.ChartData (r+s) r s A) (a : A)
    (z : CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A) :
    symmetricChartCurrentMap c (a • z) = a • symmetricChartCurrentMap c z := by
  change symmetricChartEquiv c (a • z) = a • symmetricChartEquiv c z
  exact (symmetricChartEquiv c).map_smul a z

theorem exteriorChartCurrentMap_smul (c : Collision.ChartData (r+s) r s A) (a : A)
    (z : CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A) :
    exteriorChartCurrentMap c (a • z) = a • exteriorChartCurrentMap c z := by
  change exteriorChartEquiv c (a • z) = a • exteriorChartEquiv c z
  exact (exteriorChartEquiv c).map_smul a z

end KhanSL2.SymmetricFamily
