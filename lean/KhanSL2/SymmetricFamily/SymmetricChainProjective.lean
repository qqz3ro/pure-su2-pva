module

public import KhanSL2.SymmetricFamily.SymmetricChainLabelled

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

/-! The original relative CE chains with symmetric current coefficients are
projective over the original coefficient ring, by an equivariant split retract. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open BGG BGGBridge Macdonald PolynomialBGG Conditional Factorization
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

def symmetricChainSectionRaw (k : ℕ) : ChainN (symmetricPower k) →ₗ[ℂ] SymmetricLabelledChain k :=
  (LinearMap.rTensor PositiveCE.Cochain (symmetricToTensor k)).comp
    (TensorProduct.comm ℂ PositiveCE.Cochain (symmetricPower k)).toLinearMap

def symmetricChainRetractionRaw (k : ℕ) : SymmetricLabelledChain k →ₗ[ℂ] ChainN (symmetricPower k) :=
  (TensorProduct.comm ℂ (symmetricPower k) PositiveCE.Cochain).toLinearMap.comp
    (LinearMap.rTensor PositiveCE.Cochain (tensorToSymmetric k))

@[simp] theorem symmetricChainSectionRaw_tmul (k : ℕ) (ω : PositiveCE.Cochain)
    (p : symmetricPower k) :
    symmetricChainSectionRaw k (ω ⊗ₜ[ℂ] p) = symmetricToTensor k p ⊗ₜ[ℂ] ω := rfl

@[simp] theorem symmetricChainRetractionRaw_tmul (k : ℕ)
    (u : ⨂[ℂ]^k BGG.Current) (ω : PositiveCE.Cochain) :
    symmetricChainRetractionRaw k (u ⊗ₜ[ℂ] ω) = ω ⊗ₜ[ℂ] tensorToSymmetric k u := rfl

theorem symmetricChain_raw_split (k : ℕ) (z : ChainN (symmetricPower k)) :
    symmetricChainRetractionRaw k (symmetricChainSectionRaw k z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul ω p => simp only [symmetricChainSectionRaw_tmul,
      symmetricChainRetractionRaw_tmul,tensorToSymmetric_symmetricToTensor]

theorem symmetricChainSectionRaw_act (k : ℕ) (x : G) (z : ChainN (symmetricPower k)) :
    symmetricChainSectionRaw k (actC (symmetricPower k) x z) =
      symmetricLabelledChainAct k x (symmetricChainSectionRaw k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul ω p =>
    change symmetricChainSectionRaw k (diag _ _ (ω ⊗ₜ[ℂ] p)) =
      diag (tensorDeriv k (LieModule.toEnd ℂ BGG.Current BGG.Current (constant x)))
        (ColorRoot.positiveAction x) (symmetricChainSectionRaw k (ω ⊗ₜ[ℂ] p))
    rw [diag_tmul,map_add,symmetricChainSectionRaw_tmul,symmetricChainSectionRaw_tmul,
      symmetricChainSectionRaw_tmul,diag_tmul]
    have h := symmetricToTensor_symmetricDegreeDeriv k
      (LieModule.toEnd ℂ BGG.Current BGG.Current (constant x)) p
    change symmetricToTensor k p ⊗ₜ[ℂ] ColorRoot.positiveAction x ω +
      symmetricToTensor k ⁅constant x,p⁆ ⊗ₜ[ℂ] ω = _
    change symmetricToTensor k ⁅constant x,p⁆ = _ at h
    rw [h,add_comm]

theorem symmetricChainRetractionRaw_act (k : ℕ) (x : G) (z : SymmetricLabelledChain k) :
    symmetricChainRetractionRaw k (symmetricLabelledChainAct k x z) =
      actC (symmetricPower k) x (symmetricChainRetractionRaw k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul u ω =>
    change symmetricChainRetractionRaw k (diag _ _ (u ⊗ₜ[ℂ] ω)) = diag _ _ _
    rw [diag_tmul,map_add,symmetricChainRetractionRaw_tmul,symmetricChainRetractionRaw_tmul,
      symmetricChainRetractionRaw_tmul,diag_tmul]
    rw [tensorToSymmetric_tensorDeriv]
    exact add_comm _ _

def symmetricChainSection (k : ℕ) : RelativeChains (symmetricPower k) →ₗ[ℂ]
    (SymmetricLabelledChain k ⧸ symmetricLabelledChainRelations k) :=
  (relC (symmetricPower k)).liftQ
    (((symmetricLabelledChainRelations k).mkQ.restrictScalars ℂ).comp
      (symmetricChainSectionRaw k)) (by
    refine iSup_le fun x => ?_
    rintro _ ⟨z,rfl⟩
    change (symmetricLabelledChainRelations k).mkQ
      (symmetricChainSectionRaw k (actC (symmetricPower k) x z)) = 0
    rw [symmetricChainSectionRaw_act,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_iSup_of_mem x ⟨symmetricChainSectionRaw k z,rfl⟩)

theorem symmetricChainSection_smul (k : ℕ) (r : CoefficientRing k)
    (z : RelativeChains (symmetricPower k)) :
    symmetricChainSection k (r • z) = r • symmetricChainSection k z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change symmetricChainSection k (r • (relC (symmetricPower k)).mkQ z) =
      r • symmetricChainSection k ((relC (symmetricPower k)).mkQ z)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,smul_add,hz,hw]
    | tmul ω p =>
      change symmetricChainSection k (r • (Submodule.Quotient.mk (ω ⊗ₜ[ℂ] p) :
        RelativeChains (symmetricPower k))) = _
      rw [coefficientChain_smul_mk_tmul]
      change (symmetricLabelledChainRelations k).mkQ (symmetricToTensor k (r • p) ⊗ₜ[ℂ] ω) =
        r • (symmetricLabelledChainRelations k).mkQ (symmetricToTensor k p ⊗ₜ[ℂ] ω)
      rw [symmetricToTensor_smul,← TensorProduct.smul_tmul',map_smul]

def symmetricChainSectionLinear (k : ℕ) : RelativeChains (symmetricPower k) →ₗ[CoefficientRing k]
    (SymmetricLabelledChain k ⧸ symmetricLabelledChainRelations k) where
  __ := (symmetricChainSection k).toAddHom
  map_smul' := symmetricChainSection_smul k

def symmetricChainRetractionToQuotient (k : ℕ) : SymmetricLabelledChain k →ₗ[CoefficientRing k]
    RelativeChains (symmetricPower k) where
  toFun z := (relC (symmetricPower k)).mkQ (symmetricChainRetractionRaw k z)
  map_add' z w := by simp
  map_smul' r z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [smul_add,map_add,hz,hw]
    | tmul u ω =>
      rw [TensorProduct.smul_tmul',symmetricChainRetractionRaw_tmul,tensorToSymmetric_smul]
      exact (coefficientChain_smul_mk_tmul (CoefficientRing k) (symmetricPower k)
        r ω (tensorToSymmetric k u)).symm

def symmetricChainRetractionLinear (k : ℕ) :
    (SymmetricLabelledChain k ⧸ symmetricLabelledChainRelations k) →ₗ[CoefficientRing k]
      RelativeChains (symmetricPower k) :=
  (symmetricLabelledChainRelations k).liftQ (symmetricChainRetractionToQuotient k) (by
    refine iSup_le fun x => ?_
    rintro _ ⟨z,rfl⟩
    change (relC (symmetricPower k)).mkQ
      (symmetricChainRetractionRaw k (symmetricLabelledChainAct k x z)) = 0
    rw [symmetricChainRetractionRaw_act,Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_iSup_of_mem x ⟨symmetricChainRetractionRaw k z,rfl⟩)

theorem symmetricChain_split (k : ℕ) :
    (symmetricChainRetractionLinear k).comp (symmetricChainSectionLinear k) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change (relC (symmetricPower k)).mkQ
      (symmetricChainRetractionRaw k (symmetricChainSectionRaw k z)) = _
    rw [symmetricChain_raw_split]
    rfl

theorem symmetricRelativeChains_projective (k : ℕ) :
    Module.Projective (CoefficientRing k) (RelativeChains (symmetricPower k)) := by
  let := symmetricLabelledChainQuotient_projective k
  exact Module.Projective.of_split (symmetricChainSectionLinear k)
    (symmetricChainRetractionLinear k) (symmetricChain_split k)

theorem symmetricRelativeDegree_projective (k j : ℕ) :
    Module.Projective (CoefficientRing k) (degree (symmetricPower k) j) := by
  let := symmetricRelativeChains_projective k
  exact Module.Projective.of_split
    (coefficientDegreeInclusionLinear (CoefficientRing k) (symmetricPower k) j)
    (coefficientDegreeComponentLinear (CoefficientRing k) (symmetricPower k) j)
    (coefficientDegreeComponent_inclusion (CoefficientRing k) (symmetricPower k) j)

theorem symmetricRelativeDegree_flat (k j : ℕ) :
    Module.Flat (CoefficientRing k) (degree (symmetricPower k) j) := by
  let := symmetricRelativeDegree_projective k j
  infer_instance

theorem symmetricRelativeComplex_flat (k j : ℕ) :
    Module.Flat (CoefficientRing k)
      ((coefficientRelativeComplex (CoefficientRing k) (symmetricPower k)).X j) :=
  symmetricRelativeDegree_flat k j

end KhanSL2.SymmetricFamily
