module

public import KhanSL2.SymmetricFamily.SymmetricChart

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

/-- Include the actual two specialized symmetric coefficients in their root coordinates. -/
def factorSymmetricTensorInclusion (c : Collision.ChartData (r+s) r s A) :
    FactorSymmetric r c.f₁ ⊗[A] FactorSymmetric s c.f₂ →ₗ[A]
      FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂ :=
  (FiberTransport.fixedVectors (R:=A) (V:=FactorColors r c.f₁ ⊗[A] FactorColors s c.f₂)
    (fun g => FiberTransport.tensorAction (factorLabelledRepresentation r c.f₁)
      (factorLabelledRepresentation s c.f₂) g)).subtype.comp
    ((factorTensorFixedEquiv c).toLinearMap.comp
      (TensorProduct.congr (factorSymmetricFixedEquiv r c.f₁)
        (factorSymmetricFixedEquiv s c.f₂)).toLinearMap)

omit [IsScalarTower ℂ (Depth.RB (r+s)) A] in
theorem factorSymmetricTensorInclusion_injective (c : Collision.ChartData (r+s) r s A) :
    Function.Injective (factorSymmetricTensorInclusion c) :=
  Subtype.val_injective.comp ((factorTensorFixedEquiv c).injective.comp
    (TensorProduct.congr (factorSymmetricFixedEquiv r c.f₁)
      (factorSymmetricFixedEquiv s c.f₂)).injective)

omit [IsScalarTower ℂ (Depth.RB (r+s)) A] in
@[simp] theorem factorSymmetricTensorInclusion_tmul (c : Collision.ChartData (r+s) r s A)
    (x : FactorSymmetric r c.f₁) (y : FactorSymmetric s c.f₂) :
    factorSymmetricTensorInclusion c (x ⊗ₜ[A] y) =
      (factorSymmetricFixedEquiv r c.f₁ x).val ⊗ₜ[A]
        (factorSymmetricFixedEquiv s c.f₂ y).val := rfl

/-- The exact chart equivalence becomes literal first-block restriction after a faithful inclusion. -/
theorem factorSymmetricTensorInclusion_chart (c : Collision.ChartData (r+s) r s A)
    (x : CoefficientBaseChange (Depth.RB (r+s)) (symmetricPower (r+s)) A) :
    factorSymmetricTensorInclusion c (symmetricChartEquiv c x) =
      coloredBlockTensorEquiv c
        (coloredAssignmentSplitting (r+s) A c (symmetricCoefficientRootInclusion (r+s) A x)
          (firstBlock r s)) := by
  change ((factorTensorFixedEquiv c)
    ((TensorProduct.congr (factorSymmetricFixedEquiv r c.f₁) (factorSymmetricFixedEquiv s c.f₂))
      ((TensorProduct.congr (factorSymmetricFixedEquiv r c.f₁).symm
        (factorSymmetricFixedEquiv s c.f₂).symm)
          ((factorTensorFixedEquiv c).symm (symmetricChartFixedEquiv c x))))).val = _
  rw [← TensorProduct.congr_symm,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  exact symmetricChartFixedEquiv_apply c x

end KhanSL2.SymmetricFamily
