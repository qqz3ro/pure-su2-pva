module

public import KhanSL2.SymmetricFamily.ExteriorChartInclusion
public import KhanSL2.SymmetricFamily.RootTensorBlocks
public import KhanSL2.SymmetricFamily.ExteriorPowerCoproduct

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-! The signed coefficient chart equivalence is the original alternating
coproduct specialized at the two factor polynomials, with exact normalization. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG
open scoped FactorRootScalars

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- Canonical insertion of original exterior coefficients in their factor specialization. -/
def factorExteriorUnit (n : ℕ) (f : Polynomial A) :
    (⋀[ℂ]^n BGG.Current) →ₗ[ℂ] FactorExterior n f := by
  letI := factorCoefficientAlgebra n f
  letI : IsScalarTower ℂ (Depth.RB n) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom n f).commutes z).symm
  exact ((coefficientBaseChangeEquiv (Depth.RB n) (⋀[ℂ]^n BGG.Current) A).symm.toLinearMap.restrictScalars ℂ).comp
    ((TensorProduct.mk (Depth.RB n) A (⋀[ℂ]^n BGG.Current) 1).restrictScalars ℂ)

theorem factorExteriorFixedEquiv_unit (n : ℕ) (f : Polynomial A) (p : ⋀[ℂ]^n BGG.Current) :
    (factorExteriorFixedEquiv n f (factorExteriorUnit n f p)).val =
      factorTensorUnit n f (exteriorToTensor BGG.Current n p) := rfl

variable {r s : ℕ} [Algebra (Depth.RB (r+s)) A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

omit [IsScalarTower ℂ (Depth.RB (r+s)) A] in
/-- Actual factor inclusion preserves the original alternating sections. -/
theorem factorExteriorTensorInclusion_specialize (c : Collision.ChartData (r+s) r s A)
    (z : (⋀[ℂ]^r BGG.Current) ⊗[ℂ] (⋀[ℂ]^s BGG.Current)) :
    factorExteriorTensorInclusion c
      (tensorOverMap (A:=A) (factorExteriorUnit r c.f₁) (factorExteriorUnit s c.f₂) z) =
      tensorOverMap (A:=A) (factorTensorUnit r c.f₁) (factorTensorUnit s c.f₂)
        (TensorProduct.map (exteriorToTensor BGG.Current r) (exteriorToTensor BGG.Current s) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    rw [tensorOverMap_tmul,factorExteriorTensorInclusion_tmul,
      factorExteriorFixedEquiv_unit,factorExteriorFixedEquiv_unit,
      TensorProduct.map_tmul,tensorOverMap_tmul]

/-- Actual signed first-block restriction is the specialized normalized alternating block. -/
theorem exteriorTensorBlock_chart (c : Collision.ChartData (r+s) r s A)
    (p : ⋀[ℂ]^(r+s) BGG.Current) :
    tensorOverMap (A:=A) (factorExteriorUnit r c.f₁) (factorExteriorUnit s c.f₂)
      (exteriorTensorBlock BGG.Current r s p) =
        exteriorChartEquiv c
          (show CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A
            from 1 ⊗ₜ[Depth.RB (r+s)] p) := by
  apply factorExteriorTensorInclusion_injective c
  rw [factorExteriorTensorInclusion_specialize,exteriorTensorBlock_section,
    factorExteriorTensorInclusion_chart]
  exact (LinearMap.congr_fun (chartTensorRootRestriction_eq c) (exteriorToTensor BGG.Current (r+s) p)).symm

/-- The exact binomial scalar relating the original alternating coproduct and its coprime chart iso. -/
theorem exteriorPowerCoproductComponent_chart (c : Collision.ChartData (r+s) r s A)
    (p : ⋀[ℂ]^(r+s) BGG.Current) :
    tensorOverMap (A:=A) (factorExteriorUnit r c.f₁) (factorExteriorUnit s c.f₂)
      (exteriorPowerCoproductComponent BGG.Current r s p) =
        (Nat.choose (r+s) r : ℂ) • exteriorChartEquiv c
          (show CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A
            from 1 ⊗ₜ[Depth.RB (r+s)] p) := by
  rw [exteriorPowerCoproductComponent_tensorBlock,map_smul,exteriorTensorBlock_chart]

end KhanSL2.SymmetricFamily
