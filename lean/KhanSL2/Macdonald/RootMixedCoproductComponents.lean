module

public import KhanSL2.Macdonald.RootBidegreeProjection
public import KhanSL2.Macdonald.RootBidegreeCoproductComparison
public import Mathlib.RingTheory.Flat.Basic

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct
namespace KhanSL2.Macdonald
open SymmetricFamily

abbrev RootOddAlgebra := ExteriorAlgebra ℂ (Polynomial ℂ)

/-- The literal tensor interchange for uncolored odd/even factors. -/
def rootMixedReorder : (RootOddAlgebra ⊗[ℂ] RootOddAlgebra) ⊗[ℂ]
    (RootEvenPolynomial ⊗[ℂ] RootEvenPolynomial) ≃ₗ[ℂ] RootMixed ⊗[ℂ] RootMixed :=
  TensorProduct.tensorTensorTensorComm ℂ _ _ _ _

/-- The original exterior shuffle and symmetric primitive coproduct, before the color-zero inclusion. -/
def rootMixedCoproduct : RootMixed →ₗ[ℂ] RootMixed ⊗[ℂ] RootMixed :=
  rootMixedReorder.toLinearMap.comp (TensorProduct.map
    (Factorization.ExteriorShuffle.shuffle (Polynomial ℂ)) polynomialPrimitive.toLinearMap)

theorem rootMixedFreeMap_reorder
    (u : RootOddAlgebra ⊗[ℂ] RootOddAlgebra)
    (v : RootEvenPolynomial ⊗[ℂ] RootEvenPolynomial) :
    TensorProduct.map rootMixedFreeMap rootMixedFreeMap (rootMixedReorder (u ⊗ₜ[ℂ] v)) =
      TensorProduct.map strongFreeRetraction strongFreeRetraction
        (mixedCoproductReorder
          (TensorProduct.map rootEvenPolynomialInclusion.toLinearMap rootEvenPolynomialInclusion.toLinearMap v ⊗ₜ[ℂ]
            TensorProduct.map rootOddExterior.toLinearMap rootOddExterior.toLinearMap u)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [TensorProduct.add_tmul,map_add,TensorProduct.tmul_add,ha,hb]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [TensorProduct.tmul_add,map_add,TensorProduct.add_tmul,hc,hd]
    | tmul c d => rfl

/-- Exact uncolored formula for the already specified free coproduct. -/
theorem strongFreePrimitiveCoproduct_rootMixed (q r : ℕ) (x : RootFreeBidegree q r) :
    strongFreePrimitiveCoproduct (rootFreeBidegreeMap q r x) =
      TensorProduct.map rootMixedFreeMap rootMixedFreeMap
        (rootMixedCoproduct (rootBidegreeValue q r x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a b =>
    have h := congrArg (TensorProduct.map strongFreeRetraction strongFreeRetraction)
      (strongFreePrimitiveCoproduct_bidegree_tmul q r a b)
    rw [strongFreeTensorRetraction_embedding] at h
    change _ = TensorProduct.map rootMixedFreeMap rootMixedFreeMap
      (rootMixedReorder (Factorization.ExteriorShuffle.shuffle (Polynomial ℂ) a.val ⊗ₜ[ℂ]
        polynomialPrimitive b.val))
    rw [rootMixedFreeMap_reorder]
    exact h

theorem rootMixedDegreeProjection_reorder (q₁ q₂ r₁ r₂ : ℕ)
    (u : RootOddAlgebra ⊗[ℂ] RootOddAlgebra)
    (v : RootEvenPolynomial ⊗[ℂ] RootEvenPolynomial) :
    TensorProduct.map (rootMixedDegreeProjection q₁ r₁) (rootMixedDegreeProjection q₂ r₂)
      (rootMixedReorder (u ⊗ₜ[ℂ] v)) = rootMixedReorder
        (TensorProduct.map (Factorization.ExteriorShuffle.degreeProjection (Polynomial ℂ) q₁)
          (Factorization.ExteriorShuffle.degreeProjection (Polynomial ℂ) q₂) u ⊗ₜ[ℂ]
          TensorProduct.map (MvPolynomial.homogeneousComponent r₁) (MvPolynomial.homogeneousComponent r₂) v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [TensorProduct.add_tmul,map_add,ha,hb]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [TensorProduct.tmul_add,map_add,hc,hd]
    | tmul c d => rfl

theorem rootBidegreeValue_reorder (q₁ q₂ r₁ r₂ : ℕ)
    (u : (⋀[ℂ]^q₁ (Polynomial ℂ)) ⊗[ℂ] (⋀[ℂ]^q₂ (Polynomial ℂ)))
    (v : RootEvenPower r₁ ⊗[ℂ] RootEvenPower r₂) :
    TensorProduct.map (rootBidegreeValue q₁ r₁) (rootBidegreeValue q₂ r₂)
      (TensorProduct.tensorTensorTensorComm ℂ _ _ _ _ (u ⊗ₜ[ℂ] v)) =
      rootMixedReorder
        (TensorProduct.map (ExteriorAlgebra.exteriorPower ℂ q₁ (Polynomial ℂ)).subtype
          (ExteriorAlgebra.exteriorPower ℂ q₂ (Polynomial ℂ)).subtype u ⊗ₜ[ℂ]
          TensorProduct.map (RootEvenPower r₁).subtype (RootEvenPower r₂).subtype v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [TensorProduct.add_tmul,map_add,ha,hb]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [TensorProduct.tmul_add,map_add,hc,hd]
    | tmul c d => rfl

/-- The two original normalizations multiply, with no further scalar hidden in the tensor interchange. -/
theorem rootMixedCoproduct_component (q₁ q₂ r₁ r₂ : ℕ)
    (x : RootFreeBidegree (q₁+q₂) (r₁+r₂)) :
    TensorProduct.map (rootMixedDegreeProjection q₁ r₁) (rootMixedDegreeProjection q₂ r₂)
      (rootMixedCoproduct (rootBidegreeValue (q₁+q₂) (r₁+r₂) x)) =
        ((Nat.choose (q₁+q₂) q₁ : ℂ) * (Nat.choose (r₁+r₂) r₁ : ℂ)) •
          TensorProduct.map (rootBidegreeValue q₁ r₁) (rootBidegreeValue q₂ r₂)
            (rootBidegreeNormalizedBlock q₁ q₂ r₁ r₂ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb,smul_add]
  | tmul a b =>
    change TensorProduct.map _ _
      (rootMixedReorder (Factorization.ExteriorShuffle.shuffle (Polynomial ℂ) a.val ⊗ₜ[ℂ]
        polynomialPrimitive b.val)) =
      _ • TensorProduct.map _ _ (TensorProduct.tensorTensorTensorComm ℂ _ _ _ _
        (rootOddNormalizedBlock q₁ q₂ a ⊗ₜ[ℂ] rootEvenNormalizedBlock r₁ r₂ b))
    rw [rootMixedDegreeProjection_reorder,rootBidegreeValue_reorder,
      Factorization.ExteriorShuffle.shuffle_component_normalized,
      ← rootOddNormalizedBlock_val]
    have he := rootEvenPrimitive_normalizedBlock r₁ r₂ b
    simp only [polynomialPrimitiveComponent,LinearMap.comp_apply,Nat.add_sub_cancel_left,AlgHom.toLinearMap_apply] at he
    rw [he,TensorProduct.smul_tmul_smul,map_smul]

/-- Coordinate projections commute with tensoring the actual uncolored inclusion. -/
theorem strongFreeBidegreeProjection_tensor_rootMixed (q₁ q₂ r₁ r₂ : ℕ)
    (z : RootMixed ⊗[ℂ] RootMixed) :
    TensorProduct.map (rootBidegreeValue q₁ r₁) (rootBidegreeValue q₂ r₂)
      (TensorProduct.map (strongFreeBidegreeProjection q₁ r₁) (strongFreeBidegreeProjection q₂ r₂)
        (TensorProduct.map rootMixedFreeMap rootMixedFreeMap z)) =
      TensorProduct.map (rootMixedDegreeProjection q₁ r₁) (rootMixedDegreeProjection q₂ r₂) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb]
  | tmul a b => simp only [TensorProduct.map_tmul,strongFreeBidegreeProjection_rootMixed]

/-- The actual free coproduct component equals the exact binomial multiple of the literal normalized block. -/
theorem strongFreePrimitiveCoproduct_bidegree_component (q₁ q₂ r₁ r₂ : ℕ)
    (x : RootFreeBidegree (q₁+q₂) (r₁+r₂)) :
    TensorProduct.map (strongFreeBidegreeProjection q₁ r₁) (strongFreeBidegreeProjection q₂ r₂)
      (strongFreePrimitiveCoproduct (rootFreeBidegreeMap (q₁+q₂) (r₁+r₂) x)) =
        ((Nat.choose (q₁+q₂) q₁ : ℂ) * (Nat.choose (r₁+r₂) r₁ : ℂ)) •
          rootBidegreeNormalizedBlock q₁ q₂ r₁ r₂ x := by
  apply TensorProduct.map_injective_of_flat_flat
    (rootBidegreeValue q₁ r₁) (rootBidegreeValue q₂ r₂)
    (rootBidegreeValue_injective q₁ r₁) (rootBidegreeValue_injective q₂ r₂)
  rw [strongFreePrimitiveCoproduct_rootMixed,strongFreeBidegreeProjection_tensor_rootMixed,
    map_smul,rootMixedCoproduct_component]

end KhanSL2.Macdonald


