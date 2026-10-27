module

public import KhanSL2.Macdonald.RootWeightedBlockRestriction
public import KhanSL2.Macdonald.RootOddBlockRestriction
public import KhanSL2.Macdonald.RootEvenBlockRestriction
public import KhanSL2.Macdonald.RootPolynomialAction
public import KhanSL2.Factorization.WeightedRootModelTensor

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct
namespace KhanSL2.Macdonald
open SymmetricFamily Factorization.WeightedRootModel

/-- The specified root comparison followed by the literal labelled polynomial inclusion. -/
def rootBidegreeWeightedMap (q r : ℕ) : RootFreeBidegree q r →ₗ[ℂ] LabelledWeightedRing q r :=
  (rawTensorEquiv q r).toLinearMap.comp (TensorProduct.map (rootOddRootMap q) (rootEvenRootMap r))

@[simp] theorem rootBidegreeWeightedMap_tmul (q r : ℕ)
    (x : ⋀[ℂ]^q (Polynomial ℂ)) (p : RootEvenPower r) :
    rootBidegreeWeightedMap q r (x ⊗ₜ[ℂ] p) =
      (MvPolynomial.rename Sum.inl (rootOddRootMap q x) : LabelledWeightedRing q r) *
        MvPolynomial.rename Sum.inr (rootEvenRootMap r p) := by
  simp [rootBidegreeWeightedMap]

theorem rootBidegreeWeightedMap_eq (q r : ℕ) (x : RootFreeBidegree q r) :
    rootBidegreeWeightedMap q r x =
      (rootHomologyModelEquiv q r (rootFreeToRootEquiv q r x)).val := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [LinearMap.map_zero,LinearEquiv.map_zero]
    exact (congrArg Subtype.val ((rootHomologyModelEquiv q r).map_zero)).symm
  | add u v hu hv => simp only [map_add,Submodule.coe_add,hu,hv]
  | tmul u v =>
    simp only [rootBidegreeWeightedMap_tmul,rootFreeToRootEquiv,TensorProduct.congr_tmul,
      rootHomologyModelEquiv_tmul]
    rfl

/-- The literal normalized block, with exterior variables preceding symmetric variables in each factor. -/
def rootBidegreeNormalizedBlock (q₁ q₂ r₁ r₂ : ℕ) :
    RootFreeBidegree (q₁+q₂) (r₁+r₂) →ₗ[ℂ]
      RootFreeBidegree q₁ r₁ ⊗[ℂ] RootFreeBidegree q₂ r₂ :=
  (TensorProduct.tensorTensorTensorComm ℂ _ _ _ _).toLinearMap.comp
    (TensorProduct.map (rootOddNormalizedBlock q₁ q₂) (rootEvenNormalizedBlock r₁ r₂))

theorem rootBidegreeWeightedMap_reorder (q₁ q₂ r₁ r₂ : ℕ)
    (u : (⋀[ℂ]^q₁ (Polynomial ℂ)) ⊗[ℂ] (⋀[ℂ]^q₂ (Polynomial ℂ)))
    (v : RootEvenPower r₁ ⊗[ℂ] RootEvenPower r₂) :
    TensorProduct.map (rootBidegreeWeightedMap q₁ r₁) (rootBidegreeWeightedMap q₂ r₂)
      (TensorProduct.tensorTensorTensorComm ℂ _ _ _ _ (u ⊗ₜ[ℂ] v)) =
      weightedRootBlockReorder q₁ q₂ r₁ r₂
        (TensorProduct.map (rootOddRootMap q₁) (rootOddRootMap q₂) u ⊗ₜ[ℂ]
          TensorProduct.map (rootEvenRootMap r₁) (rootEvenRootMap r₂) v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [TensorProduct.add_tmul,map_add,ha,hb]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [TensorProduct.tmul_add,map_add,hc,hd]
    | tmul c d => simp [weightedRootBlockReorder,rootBidegreeWeightedMap]

/-- Exact compatibility with literal weighted-root restriction; all normalization is in the block maps. -/
theorem rootBidegreeNormalizedBlock_roots (q₁ q₂ r₁ r₂ : ℕ)
    (x : RootFreeBidegree (q₁+q₂) (r₁+r₂)) :
    TensorProduct.map (rootBidegreeWeightedMap q₁ r₁) (rootBidegreeWeightedMap q₂ r₂)
      (rootBidegreeNormalizedBlock q₁ q₂ r₁ r₂ x) =
        weightedRootPolynomialBlock q₁ q₂ r₁ r₂
          (rootBidegreeWeightedMap (q₁+q₂) (r₁+r₂) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul u v =>
    simp only [rootBidegreeNormalizedBlock,LinearMap.comp_apply,TensorProduct.map_tmul,
      LinearEquiv.coe_coe]
    rw [rootBidegreeWeightedMap_reorder,rootOddNormalizedBlock_roots,rootEvenNormalizedBlock_roots,
      rootBidegreeWeightedMap_tmul,weightedRootPolynomialBlock_product]

end KhanSL2.Macdonald

