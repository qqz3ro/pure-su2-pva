module

public import KhanSL2.Macdonald.SymmetricCoefficientsCoproduct
public import KhanSL2.Macdonald.SymmetricCoefficientsProjection

@[expose] public section

/-! The actual (k1,k2) component of the symmetric-current coproduct, with
source the degree k1+k2 coefficient module. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

/-- The canonical homogeneous component of the primitive coproduct. -/
def symmetricCoproductComponent (k1 k2 : ℕ) :
    symmetricPower (k1+k2) →ₗ⁅ℂ,BGG.Current⁆ symmetricPower k1 ⊗[ℂ] symmetricPower k2 :=
  ((TensorProduct.LieModule.map (symmetricPowerProjection k1) (symmetricPowerProjection k2)).comp
    symmetricCoproduct).comp (symmetricPower (k1+k2)).incl

@[simp] theorem symmetricCoproductComponent_apply (k1 k2 : ℕ)
    (p : symmetricPower (k1+k2)) :
    symmetricCoproductComponent k1 k2 p =
      TensorProduct.map (symmetricPowerProjection k1).toLinearMap
        (symmetricPowerProjection k2).toLinearMap (symmetricCoproduct (p : SymmetricCoefficients)) :=
  rfl

/-- Each homogeneous coproduct component respects the coefficient coderivation identity. -/
theorem symmetricCoproductComponent_coefficientEnd (m k1 k2 : ℕ)
    (p : symmetricPower (k1+k2)) :
    symmetricCoproductComponent k1 k2 (symmetricPowerCoefficientEnd m (k1+k2) p) =
      ((symmetricPowerCoefficientEnd m k1).toLinearMap.rTensor (symmetricPower k2) +
        (symmetricPowerCoefficientEnd m k2).toLinearMap.lTensor (symmetricPower k1))
          (symmetricCoproductComponent k1 k2 p) := by
  have ht (t : SymmetricCoefficients ⊗[ℂ] SymmetricCoefficients) :
      TensorProduct.map (symmetricPowerProjection k1).toLinearMap
        (symmetricPowerProjection k2).toLinearMap
          (((symmetricCoefficientEnd m).toLinearMap.rTensor SymmetricCoefficients +
            (symmetricCoefficientEnd m).toLinearMap.lTensor SymmetricCoefficients) t) =
      ((symmetricPowerCoefficientEnd m k1).toLinearMap.rTensor (symmetricPower k2) +
        (symmetricPowerCoefficientEnd m k2).toLinearMap.lTensor (symmetricPower k1))
          (TensorProduct.map (symmetricPowerProjection k1).toLinearMap
            (symmetricPowerProjection k2).toLinearMap t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t u ht hu => simp only [map_add, ht, hu]
    | tmul u v =>
      simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
        map_add, TensorProduct.map_tmul, LieModuleHom.coe_toLinearMap,
        symmetricPowerProjection_coefficientEnd]
  rw [symmetricCoproductComponent_apply]
  change TensorProduct.map (symmetricPowerProjection k1).toLinearMap
    (symmetricPowerProjection k2).toLinearMap
      (symmetricCoproduct (symmetricCoefficientEnd m (p : SymmetricCoefficients))) = _
  rw [symmetricCoproduct_coefficientEnd]
  exact ht (symmetricCoproduct (p : SymmetricCoefficients))

end KhanSL2.Macdonald
