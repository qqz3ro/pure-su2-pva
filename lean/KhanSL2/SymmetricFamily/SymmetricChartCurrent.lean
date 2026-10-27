module

public import KhanSL2.SymmetricFamily.RootTensorBlocks
public import KhanSL2.SymmetricFamily.FactorCurrent
public import KhanSL2.SymmetricFamily.CoefficientMapRecognition

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The original coprime-chart comparison is an equivalence of the actual
current modules. Equivariance follows from its proved equality to the original
primitive coproduct, not from transporting a new action. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- The original primitive coefficient coproduct followed by genuine factor specialization. -/
def specializedSymmetricCoproduct (c : Collision.ChartData (r+s) r s A) :
    symmetricPower (r+s) →ₗ⁅ℂ,BGG.Current⁆
      BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) :=
  (tensorOverLieHom (A:=A) (factorSymmetricUnitLieHom r c.f₁)
    (factorSymmetricUnitLieHom s c.f₂)).comp (symmetricCoproductComponent r s)

/-- The specified coproduct has the exact normalized root-chart value. -/
theorem specializedSymmetricCoproduct_chart (c : Collision.ChartData (r+s) r s A)
    (p : symmetricPower (r+s)) :
    specializedSymmetricCoproduct c p = (Nat.choose (r+s) r : ℂ) •
      (show BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) from
        symmetricChartEquiv c (coefficientBaseChangeUnit (Depth.RB (r+s)) (symmetricPower (r+s)) A p)) := by
  change tensorOverLieHom (A:=A) (factorSymmetricUnitLieHom r c.f₁)
    (factorSymmetricUnitLieHom s c.f₂) (symmetricCoproductComponent r s p) = _
  rw [tensorOverLieHom_apply]
  exact symmetricCoproductComponent_chart c p

/-- Current-equivariance on the original coefficient generators of the scalar extension. -/
theorem symmetricChartEquiv_lie_unit (c : Collision.ChartData (r+s) r s A)
    (x : BGG.Current) (p : symmetricPower (r+s)) :
    (show BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) from
      symmetricChartEquiv c (coefficientBaseChangeUnit (Depth.RB (r+s)) (symmetricPower (r+s)) A ⁅x,p⁆)) =
      ⁅x,(show BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) from
        symmetricChartEquiv c (coefficientBaseChangeUnit (Depth.RB (r+s)) (symmetricPower (r+s)) A p))⁆ := by
  apply smul_right_injective _ (show (Nat.choose (r+s) r : ℂ) ≠ 0 from
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (Nat.le_add_right r s))))
  exact (specializedSymmetricCoproduct_chart c ⁅x,p⁆).symm.trans
    (((specializedSymmetricCoproduct c).map_lie x p).trans
      ((congrArg (fun z : BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) => ⁅x,z⁆)
        (specializedSymmetricCoproduct_chart c p)).trans (lie_smul _ _ _)))

/-- The actual A-linear chart map commutes with the original current actions on all tensors. -/
def symmetricChartCurrentMap (c : Collision.ChartData (r+s) r s A) :
    CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A →ₗ⁅ℂ,BGG.Current⁆
      BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) :=
  coefficientMapRecognition (Depth.RB (r+s)) (symmetricPower (r+s)) A
    (BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂))
    (symmetricChartEquiv c).toLinearMap (symmetricChartEquiv_lie_unit c)

/-- The specified normalized chart comparison is an actual current-module equivalence. -/
def symmetricChartCurrentEquiv (c : Collision.ChartData (r+s) r s A) :
    CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A ≃ₗ⁅ℂ,BGG.Current⁆
      BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) :=
  { (show CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A ≃ₗ[ℂ]
      BalancedCoefficients A (FactorSymmetric r c.f₁) (FactorSymmetric s c.f₂) from
        (symmetricChartEquiv c).restrictScalars ℂ) with
    map_lie' := (symmetricChartCurrentMap c).map_lie' }

end KhanSL2.SymmetricFamily
