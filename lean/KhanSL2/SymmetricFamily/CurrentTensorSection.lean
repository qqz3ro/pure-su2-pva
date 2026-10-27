module

public import KhanSL2.SymmetricFamily.CurrentTensorBlocks

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The original normalized section commutes with literal tensor-block
restriction on symmetric coefficients. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Macdonald

/-- In the actual current basis, multiplication followed by the normalized
section is the unchanged normalized word average. -/
theorem currentWordBasis_repr_symmetrize (k : ℕ) :
    ((currentWordBasis k).repr.toLinearMap.comp (symmetricToTensor k)).comp
      (tensorToSymmetric k) = (wordAverage k).comp (currentWordBasis k).repr.toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply,symmetricToTensor,tensorToSymmetric,LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply,relabel_unlabel]

/-- Restricting the original normalized symmetric section to two blocks
already lies in their separate normalized invariant sections. -/
theorem symmetricTensorBlock_section (r s : ℕ) (p : symmetricPower (r+s)) :
    TensorProduct.map (symmetricToTensor r) (symmetricToTensor s)
      (symmetricTensorBlock r s p) =
        tensorSlotsBlockEquiv BGG.Current r s (symmetricToTensor (r+s) p) := by
  apply (TensorProduct.congr (currentWordBasis r).repr (currentWordBasis s).repr).injective
  change TensorProduct.map (currentWordBasis r).repr.toLinearMap (currentWordBasis s).repr.toLinearMap
    (TensorProduct.map (symmetricToTensor r) (symmetricToTensor s)
      (TensorProduct.map (tensorToSymmetric r) (tensorToSymmetric s)
        (tensorSlotsBlockEquiv BGG.Current r s (symmetricToTensor (r+s) p)))) =
      TensorProduct.map (currentWordBasis r).repr.toLinearMap (currentWordBasis s).repr.toLinearMap
        (tensorSlotsBlockEquiv BGG.Current r s (symmetricToTensor (r+s) p))
  rw [TensorProduct.map_map,TensorProduct.map_map,
    currentWordBasis_repr_symmetrize,currentWordBasis_repr_symmetrize,
    ← TensorProduct.map_map,currentTensorBlock_words]
  exact wordBlock_average r s _ (symmetricToTensor_mem (r+s) p)

end KhanSL2.SymmetricFamily
