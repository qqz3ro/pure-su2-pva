module

public import KhanSL2.Factorization.ExteriorShuffleAssignments
public import KhanSL2.Factorization.ExteriorBlockTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! The colored assignment maps have the literal ordered-block formula. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.ExteriorShuffle
open SymmetricFamily
variable (M : Type*) [AddCommGroup M] [Module ℂ M]

@[simp] theorem splitShuffle_inr (u : Ext M) :
    splitShuffle M (ExteriorAlgebra.map (LinearMap.inr ℂ M M) u) = (1 : Ext M) ⊗ₜ[ℂ] u := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, map_smul, splitShuffle_one]
    exact (TensorProduct.tmul_smul _ _ _).symm
  | add u v hu hv => simp only [map_add, hu, hv, TensorProduct.tmul_add]
  | ι_mul u y hu =>
    rw [map_mul, ExteriorAlgebra.map_apply_ι, splitShuffle_ι_mul, hu, splitCreate_tmul]
    simp

/-- A left-colored word followed by a right-colored word is the ordinary tensor of the two words. -/
theorem splitShuffle_inl_mul_inr (u v : Ext M) :
    splitShuffle M (ExteriorAlgebra.map (LinearMap.inl ℂ M M) u *
      ExteriorAlgebra.map (LinearMap.inr ℂ M M) v) = u ⊗ₜ[ℂ] v := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one, smul_mul_assoc,
      one_mul, map_smul, splitShuffle_inr, TensorProduct.smul_tmul']
  | add u w hu hw => simp only [map_add, add_mul, hu, hw, TensorProduct.add_tmul]
  | ι_mul u y hu =>
    rw [map_mul (ExteriorAlgebra.map (LinearMap.inl ℂ M M)),
      ExteriorAlgebra.map_apply_ι, mul_assoc, splitShuffle_ι_mul, hu,
      splitCreate_tmul]
    simp

private theorem firstBlock_natAdd_not_mem (r s : ℕ) (j : Fin s) :
    Fin.natAdd r j ∉ (firstBlock r s).val := by
  intro h
  rcases Finset.mem_map.mp h with ⟨i, _, hi⟩
  have hv := congrArg Fin.val hi
  change i.val = r + j.val at hv
  omega

/-- The distinguished assignment has precisely the two original ordered exterior words. -/
theorem assignmentMap_firstBlock (r s : ℕ) (v : Fin (r+s) → M) :
    assignmentMap M (firstBlock r s).val (PiTensorProduct.tprod ℂ v) =
      ExteriorAlgebra.ιMulti ℂ r (fun i => v (Fin.castAdd s i)) ⊗ₜ[ℂ]
        ExteriorAlgebra.ιMulti ℂ s (fun i => v (Fin.natAdd r i)) := by
  rw [assignmentMap_tprod]
  have hv : (fun i : Fin (r+s) => if i ∈ (firstBlock r s).val then (v i, (0 : M)) else (0, v i)) =
      Fin.append (fun i => (v (Fin.castAdd s i), (0 : M)))
        (fun i => ((0 : M), v (Fin.natAdd r i))) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [firstBlock, Fin.append_left]
    · rw [if_neg (firstBlock_natAdd_not_mem r s j), Fin.append_right]
  rw [hv]
  change splitShuffle M (ExteriorAlgebra.ιMulti ℂ (r+s) _) = _
  rw [← ExteriorAlgebra.ιMulti_mul_ιMulti]
  have hleft : ExteriorAlgebra.ιMulti ℂ r (fun i => (v (Fin.castAdd s i), (0 : M))) =
      ExteriorAlgebra.map (LinearMap.inl ℂ M M)
        (ExteriorAlgebra.ιMulti ℂ r (fun i => v (Fin.castAdd s i))) := by
    rw [ExteriorAlgebra.map_apply_ιMulti]
    rfl
  have hright : ExteriorAlgebra.ιMulti ℂ s (fun i => ((0 : M), v (Fin.natAdd r i))) =
      ExteriorAlgebra.map (LinearMap.inr ℂ M M)
        (ExteriorAlgebra.ιMulti ℂ s (fun i => v (Fin.natAdd r i))) := by
    rw [ExteriorAlgebra.map_apply_ιMulti]
    rfl
  rw [hleft, hright, splitShuffle_inl_mul_inr]

/-- The assignment map agrees with the literal tensor block map on all inputs. -/
theorem assignmentMap_firstBlock_eq (r s : ℕ) :
    assignmentMap M (firstBlock r s).val = ExteriorBlock.tensorBlockMap M r s := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, assignmentMap_firstBlock,
    ExteriorBlock.tensorBlockMap_tprod, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

/-- Exact signed-average normalization, now for the actual colored assignment maps. -/
theorem sum_assignmentMap_eq_choose_signedAverage (r s : ℕ) (x : ⨂[ℂ]^(r+s) M) :
    (∑ S : Assignment (r+s) r, assignmentMap M S.val x) =
      (Nat.choose (r+s) r : ℂ) • ExteriorBlock.tensorBlockMap M r s
        (SymmetricFamily.signedAverage M (r+s) x) := by
  have h := sum_block_eq_choose_average
    (fun σ => SymmetricFamily.signedSlot M σ)
    (fun S : Assignment (r+s) r => assignmentMap M S.val)
    (fun σ S y => assignmentMap_signedSlot M σ S.val y) (firstBlock r s) x
  rw [assignmentMap_firstBlock_eq] at h
  exact h

end KhanSL2.Factorization.ExteriorShuffle
