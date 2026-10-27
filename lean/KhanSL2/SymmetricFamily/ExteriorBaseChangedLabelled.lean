module

public import KhanSL2.SymmetricFamily.ExteriorBaseChangedAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! The original exterior coefficient family over arbitrary coefficient algebras
is the signed simultaneous invariant module in the actual root/color tensors. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB k) A]

/-- Original inverse-slot permutation multiplied by its literal sign. -/
def baseSignedLabelledPermute (σ : Equiv.Perm (Fin k)) : Module.End A (BaseLabelled k A) :=
  (σ.sign : A) • baseLabelledPermute k A σ

/-- The actual root comparison preserves the signed permutation action after base change. -/
theorem baseRootTensorEquiv_signedPermute (σ : Equiv.Perm (Fin k))
    (x : A ⊗[Depth.RB k] (⨂[ℂ]^k BGG.Current)) :
    baseRootTensorEquiv k A ((tensorSignedPermutationLinear k σ).baseChange A x) =
      baseSignedLabelledPermute k A σ (baseRootTensorEquiv k A x) := by
  rw [tensorSignedPermutationLinear,LinearMap.baseChange_smul,LinearMap.smul_apply]
  rw [IsScalarTower.algebraMap_smul]
  rw [show baseRootTensorEquiv k A ((σ.sign:ℂ) • ((tensorPermutationLinear k σ).baseChange A x)) =
      (σ.sign:ℂ) • baseRootTensorEquiv k A ((tensorPermutationLinear k σ).baseChange A x) from
        ((baseRootTensorEquiv k A).restrictScalars ℂ).map_smul _ _,
    baseRootTensorEquiv_permute]
  change (σ.sign:ℂ) • baseLabelledPermute k A σ (baseRootTensorEquiv k A x) =
    (σ.sign:A) • baseLabelledPermute k A σ (baseRootTensorEquiv k A x)
  rw [← IsScalarTower.algebraMap_smul A,map_intCast]

/-- Actual exterior coefficients are exactly the signed simultaneous root/color invariants. -/
def exteriorBaseChangedLabelledEquiv :
    CoefficientBaseChange (Depth.RB k) (⋀[ℂ]^k BGG.Current) A ≃ₗ[A]
      fixedOperators (baseSignedLabelledPermute k A) :=
  (exteriorBaseChangeTensorEquiv k A).trans
    (fixedOperatorsEquiv _ _ (baseRootTensorEquiv k A) (baseRootTensorEquiv_signedPermute k A))

@[simp] theorem exteriorBaseChangedLabelledEquiv_val
    (x : CoefficientBaseChange (Depth.RB k) (⋀[ℂ]^k BGG.Current) A) :
    (exteriorBaseChangedLabelledEquiv k A x).val = exteriorCoefficientRootInclusion k A x := rfl

end KhanSL2.SymmetricFamily
