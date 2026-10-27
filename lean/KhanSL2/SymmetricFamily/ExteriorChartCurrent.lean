module

public import KhanSL2.SymmetricFamily.ExteriorBlockCurrent
public import KhanSL2.SymmetricFamily.FactorCurrent
public import KhanSL2.SymmetricFamily.CoefficientMapRecognition

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The original coprime-chart comparison is an equivalence of the actual
current modules. Equivariance follows from its proved equality to the original
alternating coproduct, not from transporting a new action. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Macdonald Factorization

/-- Canonical exterior factor insertion is an actual current-module map. -/
def factorExteriorUnitLieHom {A : Type} [CommRing A] [Algebra ℂ A]
    (n : ℕ) (f : Polynomial A) :
    (⋀[ℂ]^n BGG.Current) →ₗ⁅ℂ,BGG.Current⁆ FactorExterior n f where
  toLinearMap := factorExteriorUnit n f
  map_lie' := rfl
variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- The original canonical alternating coefficient coproduct followed by genuine factor specialization. -/
def specializedExteriorCoproduct (c : Collision.ChartData (r+s) r s A) :
    (⋀[ℂ]^(r+s) BGG.Current) →ₗ⁅ℂ,BGG.Current⁆
      BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂) :=
  (tensorOverLieHom (A:=A) (factorExteriorUnitLieHom r c.f₁)
    (factorExteriorUnitLieHom s c.f₂)).comp (exteriorPowerCoproductLieHom r s)

/-- The specified coproduct has the exact normalized root-chart value. -/
theorem specializedExteriorCoproduct_chart (c : Collision.ChartData (r+s) r s A)
    (p : (⋀[ℂ]^(r+s) BGG.Current)) :
    specializedExteriorCoproduct c p = (Nat.choose (r+s) r : ℂ) •
      (show BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂) from
        exteriorChartEquiv c (coefficientBaseChangeUnit (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A p)) := by
  change tensorOverLieHom (A:=A) (factorExteriorUnitLieHom r c.f₁)
    (factorExteriorUnitLieHom s c.f₂) (exteriorPowerCoproductLieHom r s p) = _
  rw [tensorOverLieHom_apply]
  exact exteriorPowerCoproductComponent_chart c p

/-- Current-equivariance on the original coefficient generators of the scalar extension. -/
theorem exteriorChartEquiv_lie_unit (c : Collision.ChartData (r+s) r s A)
    (x : BGG.Current) (p : (⋀[ℂ]^(r+s) BGG.Current)) :
    (show BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂) from
      exteriorChartEquiv c (coefficientBaseChangeUnit (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A ⁅x,p⁆)) =
      ⁅x,(show BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂) from
        exteriorChartEquiv c (coefficientBaseChangeUnit (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A p))⁆ := by
  apply smul_right_injective _ (show (Nat.choose (r+s) r : ℂ) ≠ 0 from
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (Nat.le_add_right r s))))
  exact (specializedExteriorCoproduct_chart c ⁅x,p⁆).symm.trans
    (((specializedExteriorCoproduct c).map_lie x p).trans
      ((congrArg (fun z : BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂) => ⁅x,z⁆)
        (specializedExteriorCoproduct_chart c p)).trans (lie_smul _ _ _)))

/-- The actual A-linear chart map commutes with the original current actions on all tensors. -/
def exteriorChartCurrentMap (c : Collision.ChartData (r+s) r s A) :
    CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A →ₗ⁅ℂ,BGG.Current⁆
      BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂) :=
  coefficientMapRecognition (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A
    (BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂))
    (exteriorChartEquiv c).toLinearMap (exteriorChartEquiv_lie_unit c)

/-- The specified normalized chart comparison is an actual current-module equivalence. -/
def exteriorChartCurrentEquiv (c : Collision.ChartData (r+s) r s A) :
    CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A ≃ₗ⁅ℂ,BGG.Current⁆
      BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂) :=
  { (show CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A ≃ₗ[ℂ]
      BalancedCoefficients A (FactorExterior r c.f₁) (FactorExterior s c.f₂) from
        (exteriorChartEquiv c).restrictScalars ℂ) with
    map_lie' := (exteriorChartCurrentMap c).map_lie' }

end KhanSL2.SymmetricFamily
