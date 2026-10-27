module

public import KhanSL2.SymmetricFamily.WordBlock
public import KhanSL2.SymmetricFamily.SymmetricCurrentBlock
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The literal split of labelled current tensors and its normalized symmetric
quotient. This uses unchanged current variables and the original primitive coproduct. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Macdonald

/-- Split the actual labelled slots into two consecutive tensor blocks. -/
def tensorSlotsBlockEquiv (M : Type*) [AddCommGroup M] [Module ℂ M] (r s : ℕ) :
    (⨂[ℂ]^(r+s) M) ≃ₗ[ℂ] (⨂[ℂ]^r M) ⊗[ℂ] (⨂[ℂ]^s M) :=
  (PiTensorProduct.reindex ℂ (fun _ : Fin (r+s) => M) finSumFinEquiv.symm).trans
    (PiTensorProduct.tmulEquiv ℂ M).symm

@[simp] theorem tensorSlotsBlockEquiv_tprod (M : Type*) [AddCommGroup M] [Module ℂ M]
    (r s : ℕ) (v : Fin (r+s) → M) :
    tensorSlotsBlockEquiv M r s (PiTensorProduct.tprod ℂ v) =
      PiTensorProduct.tprod ℂ (v ∘ Fin.castAdd s) ⊗ₜ[ℂ]
        PiTensorProduct.tprod ℂ (v ∘ Fin.natAdd r) := by
  simp only [tensorSlotsBlockEquiv,LinearEquiv.trans_apply,PiTensorProduct.reindex_tprod,
    PiTensorProduct.tmulEquiv_symm_apply,Equiv.symm_symm,finSumFinEquiv_apply_left,
    finSumFinEquiv_apply_right,Function.comp_def]

/-- Splitting actual current tensors is literal ordered-word restriction in the original basis. -/
theorem currentTensorBlock_words (r s : ℕ) (x : ⨂[ℂ]^(r+s) BGG.Current) :
    TensorProduct.map (currentWordBasis r).repr.toLinearMap (currentWordBasis s).repr.toLinearMap
      (tensorSlotsBlockEquiv BGG.Current r s x) =
        wordBlock r s ((currentWordBasis (r+s)).repr x) := by
  have he : (TensorProduct.map (currentWordBasis r).repr.toLinearMap (currentWordBasis s).repr.toLinearMap).comp
      (tensorSlotsBlockEquiv BGG.Current r s).toLinearMap =
      (wordBlock r s).comp (currentWordBasis (r+s)).repr.toLinearMap := by
    apply (currentWordBasis (r+s)).ext
    intro u
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,Module.Basis.repr_self,wordBlock_single,one_smul]
    rw [currentWordBasis_apply,tensorSlotsBlockEquiv_tprod,TensorProduct.map_tmul]
    change (currentWordBasis r).repr (PiTensorProduct.tprod ℂ (fun i => symmetricCurrentBasis ((u ∘ Fin.castAdd s) i))) ⊗ₜ[ℂ]
      (currentWordBasis s).repr (PiTensorProduct.tprod ℂ (fun i => symmetricCurrentBasis ((u ∘ Fin.natAdd r) i))) = _
    rw [← currentWordBasis_apply,← currentWordBasis_apply,Module.Basis.repr_self,Module.Basis.repr_self]
  exact LinearMap.congr_fun he x

/-- Quotient the two literal blocks of the original normalized symmetric section. -/
def symmetricTensorBlock (r s : ℕ) :
    symmetricPower (r+s) →ₗ[ℂ] symmetricPower r ⊗[ℂ] symmetricPower s :=
  (TensorProduct.map (tensorToSymmetric r) (tensorToSymmetric s)).comp
    ((tensorSlotsBlockEquiv BGG.Current r s).toLinearMap.comp (symmetricToTensor (r+s)))

/-- The literal tensor quotient is exactly the original polynomial block formula. -/
theorem symmetricTensorBlock_polynomial (r s : ℕ) (p : symmetricPower (r+s)) :
    TensorProduct.map (symmetricPower r).toSubmodule.subtype (symmetricPower s).toSubmodule.subtype
      (symmetricTensorBlock r s p) = symmetricBlockPolynomial (firstBlock r s) p := by
  have he : ((TensorProduct.map (symmetricPower r).toSubmodule.subtype
      (symmetricPower s).toSubmodule.subtype).comp
      (TensorProduct.map (tensorToSymmetric r) (tensorToSymmetric s))).comp
        (tensorSlotsBlockEquiv BGG.Current r s).toLinearMap =
      (polynomialBlockWordMap (firstBlock r s)).comp (currentWordBasis (r+s)).repr.toLinearMap := by
    apply (currentWordBasis (r+s)).ext
    intro u
    change TensorProduct.map (symmetricPower r).toSubmodule.subtype (symmetricPower s).toSubmodule.subtype
      (TensorProduct.map (tensorToSymmetric r) (tensorToSymmetric s)
        (tensorSlotsBlockEquiv BGG.Current r s (currentWordBasis (r+s) u))) =
      polynomialBlockWordMap (firstBlock r s) ((currentWordBasis (r+s)).repr (currentWordBasis (r+s) u))
    rw [Module.Basis.repr_self,polynomialBlockWordMap_single,one_smul,
      subsetPolynomial_firstBlock,subsetPolynomial_secondBlock,
      currentWordBasis_apply,tensorSlotsBlockEquiv_tprod]
    simp only [TensorProduct.map_tmul,Submodule.subtype_apply,tensorToSymmetric_tprod,
      currentVariable_basis,subsetPolynomial,Function.comp_def]
  exact LinearMap.congr_fun he (symmetricToTensor (r+s) p)

/-- The original homogeneous coproduct is exactly the binomial multiple of
normalized literal tensor block multiplication. -/
theorem symmetricCoproductComponent_tensorBlock (r s : ℕ) (p : symmetricPower (r+s)) :
    symmetricCoproductComponent r s p = (Nat.choose (r+s) r : ℂ) • symmetricTensorBlock r s p := by
  apply TensorProduct.map_injective_of_flat_flat
    (symmetricPower r).toSubmodule.subtype (symmetricPower s).toSubmodule.subtype
    Subtype.val_injective Subtype.val_injective
  rw [map_smul,symmetricTensorBlock_polynomial,
    symmetricCoproductComponent_normalization r s (firstBlock r s)]

end KhanSL2.SymmetricFamily
