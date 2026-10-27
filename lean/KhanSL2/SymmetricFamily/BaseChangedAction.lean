module

public import KhanSL2.SymmetricFamily.BaseChangedLabelled
public import KhanSL2.SymmetricFamily.CoefficientBaseChange
public import KhanSL2.SymmetricFamily.CurrentSlots

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! The actual scalar-extended current action in labelled-root coordinates.
The modes are multiplication by the original roots in their original slots. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald

variable (k : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB k) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB k) A]

/-- The specified labelled mode operator after actual coefficient base change. -/
def baseLabelledModeEnd (n : ℕ) (D : Module.End ℂ BGG.G) : Module.End A (BaseLabelled k A) :=
  ∑ i : Fin k, TensorProduct.AlgebraTensorModule.map
    (LinearMap.mulLeft A (baseRoot k A i ^ n)) (colorSlot k i D)

omit [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB k) A] in
/-- Actual root multiplication on the scalar-extended root tensors. -/
theorem baseRoot_pow_mul_tmul (n : ℕ) (i : Fin k) (a : A) (p : RootPolynomial k) :
    baseRoot k A i ^ n * (a ⊗ₜ[Depth.RB k] p) =
      a ⊗ₜ[Depth.RB k] ((show RootPolynomial k from MvPolynomial.X i)^n * p) := by
  change (1 ⊗ₜ[Depth.RB k] (show RootPolynomial k from MvPolynomial.X i))^n *
    (a ⊗ₜ[Depth.RB k] p) = _
  rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The original tensor-current mode has the literal root-slot formula over A. -/
theorem baseRootTensorEquiv_mode (n : ℕ) (D : Module.End ℂ BGG.G)
    (a : A) (u : ⨂[ℂ]^k BGG.Current) :
    baseRootTensorEquiv k A (a ⊗ₜ[Depth.RB k] tensorDeriv k (modeColorEnd n D) u) =
      baseLabelledModeEnd k A n D (baseRootTensorEquiv k A (a ⊗ₜ[Depth.RB k] u)) := by
  rw [baseRootTensorEquiv_tmul, rootTensorEquiv_modeColorEnd]
  obtain ⟨q,rfl⟩ := (rootTensorEquiv k).symm.surjective u
  rw [LinearEquiv.apply_symm_apply]
  induction q using TensorProduct.induction_on with
  | zero => simp
  | add q z hq hz => simp only [map_add, TensorProduct.tmul_add, hq, hz]
  | tmul p c =>
    simp only [labelledModeEnd, LinearMap.sum_apply, TensorProduct.map_tmul,
      LinearMap.mulLeft_apply, TensorProduct.tmul_sum, map_sum,
      TensorProduct.AlgebraTensorModule.assoc_symm_tmul,
      baseRootTensorEquiv_symm_root_tmul, baseLabelledModeEnd,
      TensorProduct.AlgebraTensorModule.map_tmul, baseRoot_pow_mul_tmul]

/-- The original normalized symmetric inclusion after actual coefficient base change. -/
def symmetricCoefficientRootInclusion :
    CoefficientBaseChange (Depth.RB k) (symmetricPower k) A →ₗ[A] BaseLabelled k A :=
  (baseRootTensorEquiv k A).toLinearMap.comp ((symmetricToTensorLinear k).baseChange A)

/-- The original symmetric coefficient action has precisely the stated root-slot formula. -/
theorem symmetricCoefficientRootInclusion_mode (n : ℕ) (x : BGG.G)
    (v : CoefficientBaseChange (Depth.RB k) (symmetricPower k) A) :
    symmetricCoefficientRootInclusion k A ⁅BGG.mode n x,v⁆ =
      baseLabelledModeEnd k A n (LieAlgebra.ad ℂ BGG.G x)
        (symmetricCoefficientRootInclusion k A v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add v w hv hw => simp only [lie_add, map_add, hv, hw]
  | tmul a p =>
    change baseRootTensorEquiv k A (a ⊗ₜ[Depth.RB k] symmetricToTensor k ⁅BGG.mode n x,p⁆) =
      baseLabelledModeEnd k A n (LieAlgebra.ad ℂ BGG.G x)
        (baseRootTensorEquiv k A (a ⊗ₜ[Depth.RB k] symmetricToTensor k p))
    rw [show symmetricToTensor k ⁅BGG.mode n x,p⁆ =
      tensorDeriv k (modeColorEnd n (LieAlgebra.ad ℂ BGG.G x)) (symmetricToTensor k p) from by
        rw [← ad_mode_eq_modeColorEnd]
        exact symmetricToTensor_symmetricDegreeDeriv k (LieAlgebra.ad ℂ BGG.Current (BGG.mode n x)) p]
    exact baseRootTensorEquiv_mode k A n (LieAlgebra.ad ℂ BGG.G x) a (symmetricToTensor k p)

end KhanSL2.SymmetricFamily
