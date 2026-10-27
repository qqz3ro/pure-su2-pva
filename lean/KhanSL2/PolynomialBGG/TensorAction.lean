module

public import KhanSL2.PolynomialBGG.TensorColors
public import KhanSL2.Conditional.BGGAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.PolynomialBGG
open BGG Current Conditional
open scoped KhanSL2.Conditional

/-- The labelled tensor coefficient action transported from root-polynomial multiplication. -/
def tensorCoefficientAction (B : ℕ) :
    CoefficientRing B →ₐ[ℂ] Module.End ℂ (⨂[ℂ]^B Cur) :=
  ((rootTensorEquiv B).symm.conjAlgEquiv ℂ).toAlgHom.comp
    (Algebra.lsmul ℂ ℂ (RootPolynomial B ⊗[ℂ] Color B))

instance tensorCoefficientModule (B : ℕ) : Module (CoefficientRing B) (⨂[ℂ]^B Cur) :=
  Module.compHom (⨂[ℂ]^B Cur) (tensorCoefficientAction B).toRingHom

@[simp] theorem tensorCoefficient_smul_eq (B : ℕ) (r : CoefficientRing B)
    (x : ⨂[ℂ]^B Cur) :
    r • x = (rootTensorEquiv B).symm (r • rootTensorEquiv B x) := rfl

instance tensorCoefficientSMulCommClass (B : ℕ) :
    SMulCommClass ℂ (CoefficientRing B) (⨂[ℂ]^B Cur) where
  smul_comm c r x := (map_smul (tensorCoefficientAction B r) c x).symm

instance tensorCoefficientIsScalarTower (B : ℕ) :
    IsScalarTower ℂ (CoefficientRing B) (⨂[ℂ]^B Cur) where
  smul_assoc c r x :=
    LinearMap.congr_fun ((tensorCoefficientAction B).toLinearMap.map_smul c r) x

@[simp] theorem rootTensorEquiv_smul (B : ℕ) (r : CoefficientRing B) (x : ⨂[ℂ]^B Cur) :
    rootTensorEquiv B (r • x) = r • rootTensorEquiv B x := by
  rw [tensorCoefficient_smul_eq, LinearEquiv.apply_symm_apply]

/-- The tensor model is an equivalence over the fixed coefficient ring. -/
def rootTensorLinearEquiv (B : ℕ) :
    (⨂[ℂ]^B Cur) ≃ₗ[CoefficientRing B] RootPolynomial B ⊗[ℂ] Color B where
  __ := (rootTensorEquiv B).toAddEquiv
  map_smul' := rootTensorEquiv_smul B

/-- The independent power-sum coordinate has its specified root-polynomial value. -/
theorem rootMap_coefficientCoordinates_X (B : ℕ) (i : Fin B) :
    rootMap B (coefficientCoordinates B (MvPolynomial.X i)) =
      (show RootPolynomial B from MvPolynomial.psum (Fin B) ℂ (i.val+1)) := by
  change ((Modules.elementaryAlgEquiv B (coefficientCoordinates B (MvPolynomial.X i))) : MvPolynomial (Fin B) ℂ) = _
  simp only [coefficientCoordinates, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
    Modules.powerSumAlgEquiv_X, Modules.powerSum]

/-- The transported action agrees with the actual sum of single-slot coefficient shifts. -/
theorem tensorCoefficientCoordinates_smul (B : ℕ) (i : Fin B) (x : ⨂[ℂ]^B Cur) :
    coefficientCoordinates B (MvPolynomial.X i) • x =
      tensorDeriv B (Modules.coefficientShift (i.val+1)) x := by
  apply (rootTensorEquiv B).injective
  rw [rootTensorEquiv_smul, rootTensorEquiv_coefficientShift]
  have he : (Algebra.lsmul ℂ ℂ (RootPolynomial B ⊗[ℂ] Color B))
      (coefficientCoordinates B (MvPolynomial.X i)) =
      LinearMap.rTensor (Color B)
        (LinearMap.mulLeft ℂ (show RootPolynomial B from MvPolynomial.psum (Fin B) ℂ (i.val+1))) := by
    apply TensorProduct.ext'
    intro f c
    simp only [Algebra.lsmul_apply, TensorProduct.smul_tmul', LinearMap.rTensor_tmul,
      LinearMap.mulLeft_apply]
    change ((rootMap B (coefficientCoordinates B (MvPolynomial.X i))) * f) ⊗ₜ[ℂ] c = _
    rw [rootMap_coefficientCoordinates_X]
  exact LinearMap.congr_fun he (rootTensorEquiv B x)

/-- Constant Lie operators commute with the coefficient-ring action on labelled tensors. -/
theorem tensorConstantLie_smul (B : ℕ) (x : G) (r : CoefficientRing B)
    (v : ⨂[ℂ]^B Cur) :
    tensorDeriv B (LieModule.toEnd ℂ Cur Cur (constant x)) (r • v) =
      r • tensorDeriv B (LieModule.toEnd ℂ Cur Cur (constant x)) v := by
  apply (rootTensorEquiv B).injective
  simp only [rootTensorEquiv_constantLie, rootTensorEquiv_smul]
  exact (TensorProduct.AlgebraTensorModule.lTensor (CoefficientRing B) (RootPolynomial B)
    (colorDeriv B (LieModule.toEnd ℂ G G x))).map_smul r (rootTensorEquiv B v)

end KhanSL2.PolynomialBGG
