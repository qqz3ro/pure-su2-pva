module

public import KhanSL2.Macdonald.RootFreeWeightedCoproduct

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct BigOperators
namespace KhanSL2.Macdonald
open SymmetricFamily

/-- The original shuffle has no component whose two exterior degrees do not sum to the input degree. -/
theorem rootOddCoproduct_offdegree (n a b : ℕ) (h : n ≠ a+b)
    (x : ⋀[ℂ]^n (Polynomial ℂ)) :
    TensorProduct.map (Factorization.ExteriorShuffle.degreeProjection (Polynomial ℂ) a)
      (Factorization.ExteriorShuffle.degreeProjection (Polynomial ℂ) b)
      (Factorization.ExteriorShuffle.shuffle (Polynomial ℂ) x.val) = 0 := by
  have hl : ((TensorProduct.map
      (Factorization.ExteriorShuffle.degreeProjection (Polynomial ℂ) a)
      (Factorization.ExteriorShuffle.degreeProjection (Polynomial ℂ) b)).comp
      (Factorization.ExteriorShuffle.shuffle (Polynomial ℂ))).comp
        (ExteriorAlgebra.exteriorPower ℂ n (Polynomial ℂ)).subtype = 0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change TensorProduct.map _ _ (Factorization.ExteriorShuffle.shuffle (Polynomial ℂ)
      (ExteriorAlgebra.ιMulti ℂ n v)) = 0
    rw [Factorization.ExteriorShuffle.shuffle_ιMulti_assignments,map_sum]
    apply Finset.sum_eq_zero
    intro S _
    rw [Factorization.ExteriorShuffle.assignmentMap_projectors (Polynomial ℂ) a b n _ _
      (Factorization.ExteriorShuffle.degreeProjection_ιMulti (Polynomial ℂ) a)
      (Factorization.ExteriorShuffle.degreeProjection_ιMulti (Polynomial ℂ) b)]
    apply if_neg
    have hs : S.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
    omega
  exact LinearMap.congr_fun hl x

/-- The primitive polynomial coproduct preserves the sum of its two homogeneous degrees. -/
theorem rootEvenCoproduct_offdegree (n a b : ℕ) (h : n ≠ a+b) (p : RootEvenPower n) :
    TensorProduct.map (MvPolynomial.homogeneousComponent a) (MvPolynomial.homogeneousComponent b)
      (polynomialPrimitive p.val) = 0 := by
  have hw (u : Fin n → ℕ) :
      TensorProduct.map (MvPolynomial.homogeneousComponent a) (MvPolynomial.homogeneousComponent b)
        (polynomialPrimitive (subsetPolynomial u Finset.univ)) = 0 := by
    rw [polynomialPrimitive_word,map_sum]
    apply Finset.sum_eq_zero
    intro S _
    rw [TensorProduct.map_tmul,
      MvPolynomial.homogeneousComponent_of_mem (subsetPolynomial_mem_degree u S),
      MvPolynomial.homogeneousComponent_of_mem (subsetPolynomial_mem_degree u Sᶜ)]
    have hs : S.card + Sᶜ.card = n := by simp
    by_cases ha : a=S.card
    · have hb : b ≠ Sᶜ.card := by omega
      rw [if_pos ha,if_neg hb,TensorProduct.tmul_zero]
    · rw [if_neg ha,TensorProduct.zero_tmul]
  have hv (v : WordSpace ℕ n) :
      TensorProduct.map (MvPolynomial.homogeneousComponent a) (MvPolynomial.homogeneousComponent b)
        (polynomialPrimitive (polynomialWordMap n v)) = 0 := by
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add,hv,hw,add_zero]
    | single u c => rw [polynomialWordMap_single,map_smul,map_smul,hw,smul_zero]
  have hp : polynomialWordMap n (rootEvenWordSection n p) = p.val := by
    rw [← rootEvenWordQuotient_val]
    change (((rootEvenExponentEquiv n).symm
      (unlabel n (relabel n (rootEvenExponentEquiv n p))))).val = p.val
    rw [unlabel_relabel,LinearEquiv.symm_apply_apply]
  rw [← hp]
  exact hv _

/-- The concrete mixed coproduct has no component of a different total odd/even bidegree. -/
theorem rootMixedCoproduct_offbidegree (q r q₁ q₂ r₁ r₂ : ℕ)
    (h : ¬(q=q₁+q₂ ∧ r=r₁+r₂)) (x : RootFreeBidegree q r) :
    TensorProduct.map (rootMixedDegreeProjection q₁ r₁) (rootMixedDegreeProjection q₂ r₂)
      (rootMixedCoproduct (rootBidegreeValue q r x)) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb,add_zero]
  | tmul a b =>
    change TensorProduct.map _ _
      (rootMixedReorder (Factorization.ExteriorShuffle.shuffle (Polynomial ℂ) a.val ⊗ₜ[ℂ]
        polynomialPrimitive b.val)) = 0
    rw [rootMixedDegreeProjection_reorder]
    by_cases hq : q=q₁+q₂
    · have hr : r ≠ r₁+r₂ := fun hr => h ⟨hq,hr⟩
      rw [rootEvenCoproduct_offdegree r r₁ r₂ hr,TensorProduct.tmul_zero,map_zero]
    · rw [rootOddCoproduct_offdegree q q₁ q₂ hq,TensorProduct.zero_tmul,map_zero]

/-- Off-bidegree vanishing for the existing free primitive coproduct and existing coordinate projections. -/
theorem strongFreePrimitiveCoproduct_offbidegree (q r q₁ q₂ r₁ r₂ : ℕ)
    (h : ¬(q=q₁+q₂ ∧ r=r₁+r₂)) (x : RootFreeBidegree q r) :
    TensorProduct.map (strongFreeBidegreeProjection q₁ r₁) (strongFreeBidegreeProjection q₂ r₂)
      (strongFreePrimitiveCoproduct (rootFreeBidegreeMap q r x)) = 0 := by
  apply TensorProduct.map_injective_of_flat_flat
    (rootBidegreeValue q₁ r₁) (rootBidegreeValue q₂ r₂)
    (rootBidegreeValue_injective q₁ r₁) (rootBidegreeValue_injective q₂ r₂)
  rw [strongFreePrimitiveCoproduct_rootMixed,strongFreeBidegreeProjection_tensor_rootMixed,
    map_zero,rootMixedCoproduct_offbidegree q r q₁ q₂ r₁ r₂ h]

/-- Off-bidegree vanishing in the original alternating/symmetric root coordinates. -/
theorem strongFreePrimitiveCoproduct_root_offbidegree (q r q₁ q₂ r₁ r₂ : ℕ)
    (h : ¬(q=q₁+q₂ ∧ r=r₁+r₂)) (x : RootFreeBidegree q r) :
    TensorProduct.map (strongFreeRootProjection (q₁,r₁)) (strongFreeRootProjection (q₂,r₂))
      (strongFreePrimitiveCoproduct (rootFreeBidegreeMap q r x)) = 0 := by
  have hmap (u v : ℕ) : (rootFreeToRootEquiv u v).toLinearMap.comp
      (strongFreeBidegreeProjection u v) = strongFreeRootProjection (u,v) :=
    LinearMap.ext (strongFreeRootProjection_bidegreeProjection u v)
  have hh := congrArg (TensorProduct.map (rootFreeToRootEquiv q₁ r₁).toLinearMap
      (rootFreeToRootEquiv q₂ r₂).toLinearMap)
    (strongFreePrimitiveCoproduct_offbidegree q r q₁ q₂ r₁ r₂ h x)
  rw [map_zero] at hh
  change ((TensorProduct.map (rootFreeToRootEquiv q₁ r₁).toLinearMap (rootFreeToRootEquiv q₂ r₂).toLinearMap).comp
    (TensorProduct.map (strongFreeBidegreeProjection q₁ r₁) (strongFreeBidegreeProjection q₂ r₂))) _ = 0 at hh
  rw [← TensorProduct.map_comp,hmap,hmap] at hh
  exact hh

/-- The complete root component formula for arbitrary input in the original free source. -/
theorem strongFreePrimitiveCoproduct_root_projection (q₁ q₂ r₁ r₂ : ℕ) (z : strongFree) :
    TensorProduct.map (strongFreeRootProjection (q₁,r₁)) (strongFreeRootProjection (q₂,r₂))
      (strongFreePrimitiveCoproduct z) =
      ((Nat.choose (q₁+q₂) q₁ : ℂ) * (Nat.choose (r₁+r₂) r₁ : ℂ)) •
        rootHomologyNormalizedBlock q₁ q₂ r₁ r₂
          (strongFreeRootProjection (q₁+q₂,r₁+r₂) z) := by
  obtain ⟨y,rfl⟩ := strongFreeRootEquiv.symm.surjective z
  induction y using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add,ha,hb,smul_add]
  | of d x =>
    have hi : strongFreeRootEquiv.symm
        (DirectSum.of (fun e : ℕ × ℕ => RootHomologyModel e.1 e.2) d x) =
        rootFreeBidegreeMap d.1 d.2 ((rootFreeToRootEquiv d.1 d.2).symm x) := by
      apply strongFreeRootEquiv.symm_apply_eq.mpr
      rw [strongFreeRootEquiv_bidegreeMap,LinearEquiv.apply_symm_apply]
    rw [hi]
    by_cases hd : d=(q₁+q₂,r₁+r₂)
    · subst d
      rw [strongFreePrimitiveCoproduct_root_component,
        ← strongFreeRootProjection_bidegreeProjection,strongFreeBidegreeProjection_same,
        LinearEquiv.apply_symm_apply]
    · have h : ¬(d.1=q₁+q₂ ∧ d.2=r₁+r₂) := by
        intro he
        apply hd
        exact Prod.ext he.1 he.2
      rw [strongFreePrimitiveCoproduct_root_offbidegree d.1 d.2 q₁ q₂ r₁ r₂ h,
        ← strongFreeRootProjection_bidegreeProjection,
        strongFreeBidegreeProjection_other (q₁+q₂) (r₁+r₂) d.1 d.2 hd,
        LinearEquiv.map_zero,LinearMap.map_zero,smul_zero]

end KhanSL2.Macdonald

