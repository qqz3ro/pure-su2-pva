module

public import KhanSL2.SymmetricFamily.SymmetricChartComplex
public import KhanSL2.Factorization.CoefficientChainEquivalence
public import KhanSL2.Factorization.ScalarComplexHomotopy

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

/-! Cancellation of the genuine coefficient chart isomorphism after arbitrary
specialization. Only the already-proved nonnegative flat cone is specialized. -/
noncomputable section
open CategoryTheory HomologicalComplex
namespace KhanSL2.SymmetricFamily
open BGG Macdonald Factorization NonnegativeCone

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- The original chart current equivalence gives the actual coefficient-linear
chain isomorphism used before the balanced shuffle. -/
def symmetricChartCoefficientComplexIso (c : Collision.ChartData (r+s) r s A) :
    coefficientRelativeComplex A
      (CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A) ≅
      coefficientRelativeComplex A
        (BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)) :=
  coefficientRelativeComplexIso A (symmetricChartCurrentEquiv c) (symmetricChartCurrentMap_smul c)

/-- The scalar-extended actual balanced shuffle inherits the quasi-isomorphism
from the chart map, since the coefficient comparison is an actual isomorphism. -/
theorem balancedShuffle_scalar_quasiIso_of_chart
    (c : Collision.ChartData (r+s) r s A) [QuasiIso (symmetricChartComplex c)]
    (K : Type) [CommRing K] [Algebra A K] :
    QuasiIso (scalarMap K (balancedShuffleComplex A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂))) := by
  let e := symmetricChartCoefficientComplexIso c
  have he : QuasiIso (scalarMap K e.hom) := by
    change QuasiIso (scalarMap K (HomotopyEquiv.ofIso e).hom)
    rw [← scalarHomotopyEquiv_hom K (HomotopyEquiv.ofIso e)]
    infer_instance
  have hcomp : scalarMap K (symmetricChartComplex c) = scalarMap K e.hom ≫
      scalarMap K (balancedShuffleComplex A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)) := by
    ext j : 1
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_comp _ _
  have hq := symmetricChartComplex_specialization c K
  rw [hcomp] at hq
  let := he
  let := hq
  exact quasiIso_of_comp_left (scalarMap K e.hom)
    (scalarMap K (balancedShuffleComplex A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂)))

end KhanSL2.SymmetricFamily
