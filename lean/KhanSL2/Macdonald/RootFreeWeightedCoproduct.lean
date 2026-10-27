module

public import KhanSL2.Macdonald.RootMixedCoproductComponents

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open SymmetricFamily Factorization.WeightedRootModel

/-- The actual signed-invariant root model included in all labelled weighted polynomials. -/
def rootHomologyWeightedMap (q r : ℕ) : RootHomologyModel q r →ₗ[ℂ] LabelledWeightedRing q r :=
  (signedInvariantComplexModule q r).subtype.comp (rootHomologyModelEquiv q r).toLinearMap

theorem rootHomologyWeightedMap_free (q r : ℕ) (x : RootFreeBidegree q r) :
    rootHomologyWeightedMap q r (rootFreeToRootEquiv q r x) = rootBidegreeWeightedMap q r x :=
  (rootBidegreeWeightedMap_eq q r x).symm

/-- Literal root block restriction, with values in the original alternating/symmetric tensor models. -/
def rootHomologyNormalizedBlock (q₁ q₂ r₁ r₂ : ℕ) :
    RootHomologyModel (q₁+q₂) (r₁+r₂) →ₗ[ℂ]
      RootHomologyModel q₁ r₁ ⊗[ℂ] RootHomologyModel q₂ r₂ :=
  (TensorProduct.map (rootFreeToRootEquiv q₁ r₁).toLinearMap (rootFreeToRootEquiv q₂ r₂).toLinearMap).comp
    ((rootBidegreeNormalizedBlock q₁ q₂ r₁ r₂).comp (rootFreeToRootEquiv (q₁+q₂) (r₁+r₂)).symm.toLinearMap)

/-- The transported block map is the actual labelled-root restriction, rather than an abstract isomorphism. -/
theorem rootHomologyNormalizedBlock_weighted (q₁ q₂ r₁ r₂ : ℕ)
    (x : RootHomologyModel (q₁+q₂) (r₁+r₂)) :
    TensorProduct.map (rootHomologyWeightedMap q₁ r₁) (rootHomologyWeightedMap q₂ r₂)
      (rootHomologyNormalizedBlock q₁ q₂ r₁ r₂ x) =
      weightedRootPolynomialBlock q₁ q₂ r₁ r₂
        (rootHomologyWeightedMap (q₁+q₂) (r₁+r₂) x) := by
  have hmap (q r : ℕ) : (rootHomologyWeightedMap q r).comp (rootFreeToRootEquiv q r).toLinearMap =
      rootBidegreeWeightedMap q r := LinearMap.ext (rootHomologyWeightedMap_free q r)
  obtain ⟨y,rfl⟩ := (rootFreeToRootEquiv (q₁+q₂) (r₁+r₂)).surjective x
  change ((TensorProduct.map (rootHomologyWeightedMap q₁ r₁) (rootHomologyWeightedMap q₂ r₂)).comp
    (TensorProduct.map (rootFreeToRootEquiv q₁ r₁).toLinearMap (rootFreeToRootEquiv q₂ r₂).toLinearMap))
      (rootBidegreeNormalizedBlock q₁ q₂ r₁ r₂
        ((rootFreeToRootEquiv (q₁+q₂) (r₁+r₂)).symm (rootFreeToRootEquiv (q₁+q₂) (r₁+r₂) y))) = _
  rw [← TensorProduct.map_comp,hmap,hmap,LinearEquiv.symm_apply_apply,
    rootBidegreeNormalizedBlock_roots,rootHomologyWeightedMap_free]

theorem strongFreeRootProjection_bidegreeProjection (q r : ℕ) (x : strongFree) :
    rootFreeToRootEquiv q r (strongFreeBidegreeProjection q r x) = strongFreeRootProjection (q,r) x :=
  (rootFreeToRootEquiv q r).apply_symm_apply _

/-- Exact root-coordinate formula for the original free coproduct on a specified bidegree. -/
theorem strongFreePrimitiveCoproduct_root_component (q₁ q₂ r₁ r₂ : ℕ)
    (x : RootHomologyModel (q₁+q₂) (r₁+r₂)) :
    TensorProduct.map (strongFreeRootProjection (q₁,r₁)) (strongFreeRootProjection (q₂,r₂))
      (strongFreePrimitiveCoproduct (rootFreeBidegreeMap (q₁+q₂) (r₁+r₂)
        ((rootFreeToRootEquiv (q₁+q₂) (r₁+r₂)).symm x))) =
      ((Nat.choose (q₁+q₂) q₁ : ℂ) * (Nat.choose (r₁+r₂) r₁ : ℂ)) •
        rootHomologyNormalizedBlock q₁ q₂ r₁ r₂ x := by
  have hmap (q r : ℕ) : (rootFreeToRootEquiv q r).toLinearMap.comp
      (strongFreeBidegreeProjection q r) = strongFreeRootProjection (q,r) :=
    LinearMap.ext (strongFreeRootProjection_bidegreeProjection q r)
  have h := congrArg (TensorProduct.map (rootFreeToRootEquiv q₁ r₁).toLinearMap
      (rootFreeToRootEquiv q₂ r₂).toLinearMap)
    (strongFreePrimitiveCoproduct_bidegree_component q₁ q₂ r₁ r₂
      ((rootFreeToRootEquiv (q₁+q₂) (r₁+r₂)).symm x))
  rw [map_smul] at h
  change ((TensorProduct.map (rootFreeToRootEquiv q₁ r₁).toLinearMap (rootFreeToRootEquiv q₂ r₂).toLinearMap).comp
    (TensorProduct.map (strongFreeBidegreeProjection q₁ r₁) (strongFreeBidegreeProjection q₂ r₂))) _ = _ at h
  rw [← TensorProduct.map_comp,hmap,hmap] at h
  exact h

/-- The actual coproduct has precisely the two binomial factors times literal weighted-root restriction. -/
theorem strongFreePrimitiveCoproduct_weighted_component (q₁ q₂ r₁ r₂ : ℕ)
    (x : RootHomologyModel (q₁+q₂) (r₁+r₂)) :
    TensorProduct.map (rootHomologyWeightedMap q₁ r₁) (rootHomologyWeightedMap q₂ r₂)
      (TensorProduct.map (strongFreeRootProjection (q₁,r₁)) (strongFreeRootProjection (q₂,r₂))
        (strongFreePrimitiveCoproduct (rootFreeBidegreeMap (q₁+q₂) (r₁+r₂)
          ((rootFreeToRootEquiv (q₁+q₂) (r₁+r₂)).symm x)))) =
      ((Nat.choose (q₁+q₂) q₁ : ℂ) * (Nat.choose (r₁+r₂) r₁ : ℂ)) •
        weightedRootPolynomialBlock q₁ q₂ r₁ r₂
          (rootHomologyWeightedMap (q₁+q₂) (r₁+r₂) x) := by
  rw [strongFreePrimitiveCoproduct_root_component,map_smul,rootHomologyNormalizedBlock_weighted]

end KhanSL2.Macdonald
