module

public import KhanSL2.SymmetricFamily.BaseChangedAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! The original exterior coefficient action after arbitrary coefficient base
change, faithfully represented by the actual normalized alternating tensor section. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB k) A]

/-- The original exterior section after the prescribed coefficient scalar extension. -/
def exteriorCoefficientRootInclusion :
    CoefficientBaseChange (Depth.RB k) (⋀[ℂ]^k BGG.Current) A →ₗ[A] BaseLabelled k A :=
  (baseRootTensorEquiv k A).toLinearMap.comp ((exteriorToTensorLinear k).baseChange A)

theorem exteriorCoefficientRootInclusion_injective :
    Function.Injective (exteriorCoefficientRootInclusion k A) := by
  intro x y h
  apply (exteriorBaseChangeTensorEquiv k A).injective
  apply Subtype.ext
  exact (baseRootTensorEquiv k A).injective h

/-- The original specialized exterior current action is the literal evaluation-slot action. -/
theorem exteriorCoefficientRootInclusion_mode (n : ℕ) (x : BGG.G)
    (v : CoefficientBaseChange (Depth.RB k) (⋀[ℂ]^k BGG.Current) A) :
    exteriorCoefficientRootInclusion k A ⁅BGG.mode n x,v⁆ =
      baseLabelledModeEnd k A n (LieAlgebra.ad ℂ BGG.G x)
        (exteriorCoefficientRootInclusion k A v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [lie_add,map_add,hv,hw]
  | tmul a p =>
    change baseRootTensorEquiv k A (a ⊗ₜ[Depth.RB k] exteriorToTensor BGG.Current k ⁅BGG.mode n x,p⁆) =
      baseLabelledModeEnd k A n (LieAlgebra.ad ℂ BGG.G x)
        (baseRootTensorEquiv k A (a ⊗ₜ[Depth.RB k] exteriorToTensor BGG.Current k p))
    rw [show exteriorToTensor BGG.Current k ⁅BGG.mode n x,p⁆ =
      tensorDeriv k (modeColorEnd n (LieAlgebra.ad ℂ BGG.G x)) (exteriorToTensor BGG.Current k p) from by
        rw [exteriorCurrent_lie,← ad_mode_eq_modeColorEnd]
        exact LinearMap.congr_fun (exteriorToTensor_exteriorDeriv k
          (LieAlgebra.ad ℂ BGG.Current (BGG.mode n x))) p]
    exact baseRootTensorEquiv_mode k A n (LieAlgebra.ad ℂ BGG.G x) a (exteriorToTensor BGG.Current k p)

end KhanSL2.SymmetricFamily
