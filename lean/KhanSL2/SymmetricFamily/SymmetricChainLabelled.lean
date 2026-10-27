module

public import KhanSL2.SymmetricFamily.FiniteProjective
public import KhanSL2.PolynomialBGG.LabelledRoot
public import KhanSL2.Factorization.RelativeChainsScalarDegrees

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

/-! Polynomial-valued color coinvariants for the actual full relative CE chains.
The exterior CE factor may be infinite dimensional; no finite truncation is assumed. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open BGG BGGBridge Macdonald PolynomialBGG Conditional

abbrev SymmetricLabelledChain (k : ℕ) := (⨂[ℂ]^k BGG.Current) ⊗[ℂ] PositiveCE.Cochain
abbrev SymmetricChainColor (k : ℕ) := Color k ⊗[ℂ] PositiveCE.Cochain

instance symmetricLabelledChainAddCommGroup (k : ℕ) : AddCommGroup (SymmetricLabelledChain k) :=
  Module.addCommMonoidToAddCommGroup ℂ

instance symmetricChainColorAddCommGroup (k : ℕ) : AddCommGroup (SymmetricChainColor k) :=
  Module.addCommMonoidToAddCommGroup ℂ

def symmetricLabelledChainAct (k : ℕ) (x : G) :
    Module.End (CoefficientRing k) (SymmetricLabelledChain k) where
  toFun := diag (tensorDeriv k (LieModule.toEnd ℂ BGG.Current BGG.Current (constant x)))
    (ColorRoot.positiveAction x)
  map_add' := map_add _
  map_smul' r u := by
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => simp only [smul_add, map_add, hu, hv]
    | tmul v ω =>
      simp only [TensorProduct.smul_tmul', diag_tmul, smul_add]
      rw [tensorConstantLie_smul]
      rfl

def symmetricChainColorAct (k : ℕ) (x : G) : Module.End ℂ (SymmetricChainColor k) :=
  diag (colorDeriv k (LieModule.toEnd ℂ G G x)) (ColorRoot.positiveAction x)

def symmetricLabelledChainRootEquiv (k : ℕ) :
    SymmetricLabelledChain k ≃ₗ[CoefficientRing k]
      RootPolynomial k ⊗[ℂ] SymmetricChainColor k :=
  (TensorProduct.AlgebraTensorModule.congr (rootTensorLinearEquiv k)
    (LinearEquiv.refl ℂ PositiveCE.Cochain)).trans
    (TensorProduct.AlgebraTensorModule.assoc ℂ ℂ (CoefficientRing k)
      (RootPolynomial k) (Color k) PositiveCE.Cochain)

@[simp] theorem symmetricLabelledChainRootEquiv_tmul (k : ℕ)
    (u : ⨂[ℂ]^k BGG.Current) (ω : PositiveCE.Cochain) :
    symmetricLabelledChainRootEquiv k (u ⊗ₜ[ℂ] ω) =
      TensorProduct.AlgebraTensorModule.assoc ℂ ℂ (CoefficientRing k)
        (RootPolynomial k) (Color k) PositiveCE.Cochain
        (rootTensorEquiv k u ⊗ₜ[ℂ] ω) := rfl

@[simp] theorem symmetricLabelledChainRootEquiv_symm_tmul (k : ℕ)
    (f : RootPolynomial k) (c : Color k) (ω : PositiveCE.Cochain) :
    symmetricLabelledChainRootEquiv k ((rootTensorEquiv k).symm (f ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] ω) =
      f ⊗ₜ[ℂ] (c ⊗ₜ[ℂ] ω) := by
  rw [symmetricLabelledChainRootEquiv_tmul, LinearEquiv.apply_symm_apply]
  rfl

theorem symmetricLabelledChainRootEquiv_act (k : ℕ) (x : G)
    (u : SymmetricLabelledChain k) :
    symmetricLabelledChainRootEquiv k (symmetricLabelledChainAct k x u) =
      TensorProduct.AlgebraTensorModule.lTensor (CoefficientRing k) (RootPolynomial k)
        (symmetricChainColorAct k x) (symmetricLabelledChainRootEquiv k u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul u ω =>
    obtain ⟨w, rfl⟩ := (rootTensorEquiv k).symm.surjective u
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, TensorProduct.add_tmul, hy, hz]
    | tmul f c =>
      have hd : tensorDeriv k (LieModule.toEnd ℂ BGG.Current BGG.Current (constant x))
          ((rootTensorEquiv k).symm (f ⊗ₜ[ℂ] c)) =
          (rootTensorEquiv k).symm (f ⊗ₜ[ℂ] colorDeriv k (LieModule.toEnd ℂ G G x) c) := by
        apply (rootTensorEquiv k).injective
        rw [rootTensorEquiv_constantLie, LinearEquiv.apply_symm_apply,
          LinearEquiv.apply_symm_apply, LinearMap.lTensor_tmul]
      change symmetricLabelledChainRootEquiv k (diag _ _
        ((rootTensorEquiv k).symm (f ⊗ₜ[ℂ] c) ⊗ₜ[ℂ] ω)) = _
      rw [diag_tmul, map_add, hd, symmetricLabelledChainRootEquiv_symm_tmul,
        symmetricLabelledChainRootEquiv_symm_tmul, symmetricLabelledChainRootEquiv_symm_tmul]
      simp only [TensorProduct.AlgebraTensorModule.lTensor_tmul, symmetricChainColorAct,
        diag_tmul, TensorProduct.tmul_add]

def symmetricLabelledChainRelations (k : ℕ) :
    Submodule (CoefficientRing k) (SymmetricLabelledChain k) :=
  actionRelations (symmetricLabelledChainAct k)

def symmetricLabelledChainQuotientEquiv (k : ℕ) :
    (SymmetricLabelledChain k ⧸ symmetricLabelledChainRelations k) ≃ₗ[CoefficientRing k]
      (RootPolynomial k ⊗[ℂ] SymmetricChainColor k) ⧸
        actionRelations (fun x : G => TensorProduct.AlgebraTensorModule.lTensor
          (CoefficientRing k) (RootPolynomial k) (symmetricChainColorAct k x)) :=
  Submodule.Quotient.equiv _ _ (symmetricLabelledChainRootEquiv k)
    (actionRelations_map_equiv (symmetricLabelledChainAct k) _
      (symmetricLabelledChainRootEquiv k) (symmetricLabelledChainRootEquiv_act k))

theorem symmetricLabelledChainQuotient_projective (k : ℕ) :
    Module.Projective (CoefficientRing k)
      (SymmetricLabelledChain k ⧸ symmetricLabelledChainRelations k) := by
  have := tensorActionCoinvariants_projective (R := CoefficientRing k)
    (P := RootPolynomial k) (symmetricChainColorAct k)
  exact Module.Projective.of_equiv' (symmetricLabelledChainQuotientEquiv k).symm

end KhanSL2.SymmetricFamily
