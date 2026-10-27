module

public import KhanSL2.SymmetricFamily.ExteriorChart

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Faithful original root coordinates for the chart target, retaining the
literal canonical quotient restriction defining the chart equivalence. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald Factorization
open scoped FactorRootScalars

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

/-- Include the actual two specialized exterior coefficients in their root coordinates. -/
def factorExteriorTensorInclusion (c : Collision.ChartData (r+s) r s A) :
    FactorExterior r c.f₁ ⊗[A] FactorExterior s c.f₂ →ₗ[A]
      FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂ :=
  (FiberTransport.fixedVectors (R:=A) (V:=FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂)
    (fun g => FiberTransport.tensorAction (factorSignedLabelledRepresentation r c.f₁)
      (factorSignedLabelledRepresentation s c.f₂) g)).subtype.comp
    ((exteriorFactorTensorFixedEquiv c).toLinearMap.comp
      (TensorProduct.congr (factorExteriorFixedEquiv r c.f₁)
        (factorExteriorFixedEquiv s c.f₂)).toLinearMap)

omit [IsScalarTower ℂ (Depth.RB (r+s)) A] in
theorem factorExteriorTensorInclusion_injective (c : Collision.ChartData (r+s) r s A) :
    Function.Injective (factorExteriorTensorInclusion c) :=
  Subtype.val_injective.comp ((exteriorFactorTensorFixedEquiv c).injective.comp
    (TensorProduct.congr (factorExteriorFixedEquiv r c.f₁)
      (factorExteriorFixedEquiv s c.f₂)).injective)

omit [IsScalarTower ℂ (Depth.RB (r+s)) A] in
@[simp] theorem factorExteriorTensorInclusion_tmul (c : Collision.ChartData (r+s) r s A)
    (x : FactorExterior r c.f₁) (y : FactorExterior s c.f₂) :
    factorExteriorTensorInclusion c (x ⊗ₜ[A] y) =
      (factorExteriorFixedEquiv r c.f₁ x).val ⊗ₜ[A]
        (factorExteriorFixedEquiv s c.f₂ y).val := rfl

/-- The signed chart equivalence retains the literal actual quotient component. -/
theorem exteriorChartFixedEquiv_apply (c : Collision.ChartData (r+s) r s A)
    (x : CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A) :
    (exteriorChartFixedEquiv c x).val = coloredBlockTensorEquiv c
      (coloredAssignmentSplitting (r+s) A c (exteriorCoefficientRootInclusion (r+s) A x)
        (firstBlock r s)) := rfl
/-- The exact chart equivalence becomes literal first-block restriction after a faithful inclusion. -/
theorem factorExteriorTensorInclusion_chart (c : Collision.ChartData (r+s) r s A)
    (x : CoefficientBaseChange (Depth.RB (r+s)) (⋀[ℂ]^(r+s) BGG.Current) A) :
    factorExteriorTensorInclusion c (exteriorChartEquiv c x) =
      coloredBlockTensorEquiv c
        (coloredAssignmentSplitting (r+s) A c (exteriorCoefficientRootInclusion (r+s) A x)
          (firstBlock r s)) := by
  change ((exteriorFactorTensorFixedEquiv c)
    ((TensorProduct.congr (factorExteriorFixedEquiv r c.f₁) (factorExteriorFixedEquiv s c.f₂))
      ((TensorProduct.congr (factorExteriorFixedEquiv r c.f₁).symm
        (factorExteriorFixedEquiv s c.f₂).symm)
          ((exteriorFactorTensorFixedEquiv c).symm (exteriorChartFixedEquiv c x))))).val = _
  rw [← TensorProduct.congr_symm,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  exact exteriorChartFixedEquiv_apply c x

end KhanSL2.SymmetricFamily
