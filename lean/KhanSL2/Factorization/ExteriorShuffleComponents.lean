module

public import KhanSL2.Factorization.ExteriorShuffleBlocks
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # Actual exterior-degree components of the signed shuffle -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.ExteriorShuffle
open SymmetricFamily
variable (M : Type*) [AddCommGroup M] [Module ℂ M]

/-- The canonical homogeneous projection supplied by the exterior algebra grading. -/
def degreeProjection (r : ℕ) : Module.End ℂ (Ext M) :=
  (⋀[ℂ]^r M).subtype.comp
    ((DirectSum.component ℂ ℕ (fun j => ⋀[ℂ]^j M) r).comp
      (ExteriorAlgebra.GradedAlgebra.liftι ℂ M).toLinearMap)

theorem degreeProjection_of_mem (r d : ℕ) (u : Ext M) (hu : u ∈ ⋀[ℂ]^d M) :
    degreeProjection M r u = if d=r then u else 0 := by
  let v : ⋀[ℂ]^d M := ⟨u, hu⟩
  change degreeProjection M r (v : Ext M) = if d=r then (v : Ext M) else 0
  simp only [degreeProjection, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    ExteriorAlgebra.GradedAlgebra.liftι_eq]
  change ((DirectSum.component ℂ ℕ (fun j => ⋀[ℂ]^j M) r)
    (DirectSum.lof ℂ ℕ (fun j => ⋀[ℂ]^j M) d v) : Ext M) = _
  rw [DirectSum.component.of]
  split_ifs with h
  · subst d
    rfl
  · rfl

@[simp] theorem degreeProjection_ιMulti (r d : ℕ) (v : Fin d → M) :
    degreeProjection M r (ExteriorAlgebra.ιMulti ℂ d v) =
      if d=r then ExteriorAlgebra.ιMulti ℂ d v else 0 :=
  degreeProjection_of_mem M r d _ (ExteriorAlgebra.ιMulti_range ℂ d (Set.mem_range_self v))

/-- Degree projections distinguish assignment sizes in the actual colored expansion. -/
theorem assignmentMap_projectors (r s n : ℕ) (P Q : Module.End ℂ (Ext M))
    (hP : ∀ d (v : Fin d → M), P (ExteriorAlgebra.ιMulti ℂ d v) =
      if d=r then ExteriorAlgebra.ιMulti ℂ d v else 0)
    (hQ : ∀ d (v : Fin d → M), Q (ExteriorAlgebra.ιMulti ℂ d v) =
      if d=s then ExteriorAlgebra.ιMulti ℂ d v else 0)
    (S : Finset (Fin n)) (v : Fin n → M) :
    TensorProduct.map P Q (assignmentMap M S (PiTensorProduct.tprod ℂ v)) =
      if S.card=r ∧ n-S.card=s then assignmentMap M S (PiTensorProduct.tprod ℂ v) else 0 := by
  generalize hc : S.card = t
  have htn : t ≤ n := by
    simpa only [hc, Fintype.card_fin] using Finset.card_le_univ S
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le htn
  obtain ⟨σ, hσ⟩ := assignment_transitive (firstBlock t u) (⟨S, hc⟩ : Assignment (t+u) t)
  have hs : (firstBlock t u).val.map σ.toEmbedding = S := congrArg Subtype.val hσ
  rw [← hs, ← assignmentMap_signedSlot]
  simp only [signedSlot, LinearMap.smul_apply, LinearEquiv.coe_coe, slotPermute_tprod,
    map_smul, assignmentMap_firstBlock, TensorProduct.map_tmul, hP, hQ,
    Nat.add_sub_cancel_left]
  by_cases ht : t=r <;> by_cases hu : u=s <;>
    simp [ht, hu, TensorProduct.zero_tmul, TensorProduct.tmul_zero]

/-- Projecting the actual shuffle retains exactly the prescribed-size assignments. -/
theorem shuffle_projectors_ιMulti (r s : ℕ) (P Q : Module.End ℂ (Ext M))
    (hP : ∀ d (v : Fin d → M), P (ExteriorAlgebra.ιMulti ℂ d v) =
      if d=r then ExteriorAlgebra.ιMulti ℂ d v else 0)
    (hQ : ∀ d (v : Fin d → M), Q (ExteriorAlgebra.ιMulti ℂ d v) =
      if d=s then ExteriorAlgebra.ιMulti ℂ d v else 0)
    (v : Fin (r+s) → M) :
    TensorProduct.map P Q (shuffle M (ExteriorAlgebra.ιMulti ℂ (r+s) v)) =
      ∑ S : Assignment (r+s) r, assignmentMap M S.val (PiTensorProduct.tprod ℂ v) := by
  rw [shuffle_ιMulti_assignments, map_sum]
  simp only [assignmentMap_projectors M r s (r+s) P Q hP hQ]
  have hcond (S : Finset (Fin (r+s))) : (S.card=r ∧ r+s-S.card=s) ↔ S.card=r := by
    constructor
    · exact And.left
    · intro h
      exact ⟨h, by rw [h, Nat.add_sub_cancel_left]⟩
  simp only [hcond]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter (fun S : Finset (Fin (r+s)) => S.card=r))
    (by simp) (fun S => assignmentMap M S (PiTensorProduct.tprod ℂ v))

/-- The formula retains any original homogeneous projectors, provided their action
on exterior words is the stated degree projection. -/
theorem shuffle_projectors_normalized (r s : ℕ) (P Q : Module.End ℂ (Ext M))
    (hP : ∀ d (v : Fin d → M), P (ExteriorAlgebra.ιMulti ℂ d v) =
      if d=r then ExteriorAlgebra.ιMulti ℂ d v else 0)
    (hQ : ∀ d (v : Fin d → M), Q (ExteriorAlgebra.ιMulti ℂ d v) =
      if d=s then ExteriorAlgebra.ιMulti ℂ d v else 0)
    (x : ⋀[ℂ]^(r+s) M) :
    TensorProduct.map P Q (shuffle M (x : Ext M)) =
      (Nat.choose (r+s) r : ℂ) • ExteriorBlock.tensorBlockMap M r s
        (PolynomialBGG.exteriorToTensor M (r+s) x) := by
  have h : ((TensorProduct.map P Q).comp (shuffle M)).comp (⋀[ℂ]^(r+s) M).subtype =
      (Nat.choose (r+s) r : ℂ) •
        (ExteriorBlock.tensorBlockMap M r s).comp (PolynomialBGG.exteriorToTensor M (r+s)) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change TensorProduct.map P Q (shuffle M (ExteriorAlgebra.ιMulti ℂ (r+s) v)) = _
    rw [shuffle_projectors_ιMulti M r s P Q hP hQ,
      sum_assignmentMap_eq_choose_signedAverage]
    have ha := LinearMap.congr_fun (alternatingProjection_eq_signedAverage M (r+s))
      (PiTensorProduct.tprod ℂ v)
    simp only [LinearMap.comp_apply, PolynomialBGG.tensorToExterior_tprod] at ha
    rw [← ha]
    rfl
  exact LinearMap.congr_fun h x

/-- The actual exterior shuffle component has exactly the original binomial normalization. -/
theorem shuffle_component_normalized (r s : ℕ) (x : ⋀[ℂ]^(r+s) M) :
    TensorProduct.map (degreeProjection M r) (degreeProjection M s)
        (shuffle M (x : Ext M)) =
      (Nat.choose (r+s) r : ℂ) • ExteriorBlock.tensorBlockMap M r s
        (PolynomialBGG.exteriorToTensor M (r+s) x) :=
  shuffle_projectors_normalized M r s _ _ (degreeProjection_ιMulti M r)
    (degreeProjection_ιMulti M s) x

/-- Inverse normalization for the original tensor-block map and any verified degree projectors. -/
theorem normalized_block_eq_inv_choose_shuffle (r s : ℕ) (P Q : Module.End ℂ (Ext M))
    (hP : ∀ d (v : Fin d → M), P (ExteriorAlgebra.ιMulti ℂ d v) =
      if d=r then ExteriorAlgebra.ιMulti ℂ d v else 0)
    (hQ : ∀ d (v : Fin d → M), Q (ExteriorAlgebra.ιMulti ℂ d v) =
      if d=s then ExteriorAlgebra.ιMulti ℂ d v else 0)
    (x : ⋀[ℂ]^(r+s) M) :
    ExteriorBlock.tensorBlockMap M r s (PolynomialBGG.exteriorToTensor M (r+s) x) =
      (Nat.choose (r+s) r : ℂ)⁻¹ • TensorProduct.map P Q (shuffle M (x : Ext M)) := by
  rw [shuffle_projectors_normalized M r s P Q hP hQ, smul_smul,
    inv_mul_cancel₀ (ExteriorBlock.block_choose_ne_zero r s), one_smul]

/-- Mathlib's signed shuffle block is precisely the degree component of the
already constructed exterior shuffle; the two constructions have identical normalization. -/
theorem shuffle_component_eq_exteriorBlockMap (r s : ℕ) (x : ⋀[ℂ]^(r+s) M) :
    TensorProduct.map (degreeProjection M r) (degreeProjection M s)
        (shuffle M (x : Ext M)) = ExteriorBlock.exteriorBlockMap M r s x := by
  rw [shuffle_component_normalized, ExteriorBlock.tensorBlockMap_exteriorToTensor,
    smul_smul, mul_inv_cancel₀ (ExteriorBlock.block_choose_ne_zero r s), one_smul]

end KhanSL2.Factorization.ExteriorShuffle
