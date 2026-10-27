module

public import KhanSL2.Factorization.ShuffleExterior
public import KhanSL2.SymmetricFamily.BlockAverageNormalization

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # Colored creation operators for the actual exterior shuffle

Left/right colorings of labelled inputs are evaluations of one alternating map
on M × M. Consequently their signed-slot equivariance carries no choice of
shuffle representatives or extra sign convention.
-/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.ExteriorShuffle

variable (M : Type*) [AddCommGroup M] [Module ℂ M]

/-- Independently colored left and right creation operators. -/
def splitCreate (y : M × M) : Module.End ℂ (Tensor M) :=
  LinearMap.rTensor (Ext M) (LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ y.1)) +
    TensorProduct.map (parity M).toLinearMap (LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ y.2))

@[simp] theorem splitCreate_tmul (y : M × M) (u v : Ext M) :
    splitCreate M y (u ⊗ₜ[ℂ] v) =
      (ExteriorAlgebra.ι ℂ y.1 * u) ⊗ₜ[ℂ] v +
        parity M u ⊗ₜ[ℂ] (ExteriorAlgebra.ι ℂ y.2 * v) := rfl

def splitCreateLinear : (M × M) →ₗ[ℂ] Module.End ℂ (Tensor M) where
  toFun := splitCreate M
  map_add' y z := by
    apply TensorProduct.ext'
    intro u v
    simp only [LinearMap.add_apply, splitCreate_tmul, Prod.fst_add, Prod.snd_add,
      map_add, add_mul, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  map_smul' c y := by
    apply TensorProduct.ext'
    intro u v
    simp only [LinearMap.smul_apply, splitCreate_tmul, Prod.smul_fst, Prod.smul_snd,
      map_smul, smul_mul_assoc, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
      smul_add, RingHom.id_apply]

theorem splitCreate_square (y : M × M) : splitCreate M y * splitCreate M y = 0 := by
  apply TensorProduct.ext'
  intro u v
  simp only [Module.End.mul_apply, splitCreate_tmul, map_add, map_mul, parity_ι,
    neg_mul, parity_parity, TensorProduct.neg_tmul, ← mul_assoc,
    ExteriorAlgebra.ι_sq_zero, zero_mul, TensorProduct.zero_tmul,
    TensorProduct.tmul_zero, LinearMap.zero_apply]
  abel

/-- The square-zero colored creation representation. -/
def splitRepresentation : ExteriorAlgebra ℂ (M × M) →ₐ[ℂ] Module.End ℂ (Tensor M) :=
  ExteriorAlgebra.lift ℂ ⟨splitCreateLinear M, splitCreate_square M⟩

@[simp] theorem splitRepresentation_ι (y : M × M) :
    splitRepresentation M (ExteriorAlgebra.ι ℂ y) = splitCreate M y :=
  ExteriorAlgebra.lift_ι_apply _ _ _ y

/-- Evaluate the colored representation on the tensor unit. -/
def splitShuffle : ExteriorAlgebra ℂ (M × M) →ₗ[ℂ] Tensor M where
  toFun u := splitRepresentation M u ((1 : Ext M) ⊗ₜ[ℂ] (1 : Ext M))
  map_add' u v := by simp
  map_smul' c u := by simp

@[simp] theorem splitShuffle_one :
    splitShuffle M 1 = (1 : Ext M) ⊗ₜ[ℂ] (1 : Ext M) := by
  simp [splitShuffle]

@[simp] theorem splitShuffle_ι_mul (y : M × M) (u : ExteriorAlgebra ℂ (M × M)) :
    splitShuffle M (ExteriorAlgebra.ι ℂ y * u) = splitCreate M y (splitShuffle M u) := by
  simp only [splitShuffle, LinearMap.coe_mk, AddHom.coe_mk, map_mul,
    splitRepresentation_ι, Module.End.mul_apply]

/-- Forgetting colors by inserting each vector diagonally recovers the existing shuffle. -/
theorem splitShuffle_diagonal (u : Ext M) :
    splitShuffle M (ExteriorAlgebra.map (LinearMap.id.prod LinearMap.id) u) = shuffle M u := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, map_one, map_smul,
      splitShuffle_one, shuffle_one]
  | add u v hu hv => simp only [map_add, hu, hv]
  | ι_mul u y hu =>
    rw [map_mul, ExteriorAlgebra.map_apply_ι, splitShuffle_ι_mul, hu, shuffle_ι_mul]
    rfl

/-- The alternating map behind every left/right coloring of the exterior word. -/
def splitAlternating (n : ℕ) : (M × M) [⋀^Fin n]→ₗ[ℂ] Tensor M :=
  (splitShuffle M).compAlternatingMap (ExteriorAlgebra.ιMulti ℂ n)

/-- The literal assignment block, obtained by coloring each slot independently. -/
def assignmentMap {n : ℕ} (S : Finset (Fin n)) : (⨂[ℂ]^n M) →ₗ[ℂ] Tensor M :=
  PiTensorProduct.lift ((splitAlternating M n).toMultilinearMap.compLinearMap
    (fun i => if i ∈ S then LinearMap.inl ℂ M M else LinearMap.inr ℂ M M))

@[simp] theorem assignmentMap_tprod {n : ℕ} (S : Finset (Fin n)) (v : Fin n → M) :
    assignmentMap M S (PiTensorProduct.tprod ℂ v) =
      splitAlternating M n (fun i => if i ∈ S then (v i, 0) else (0, v i)) := by
  rw [assignmentMap, PiTensorProduct.lift.tprod]
  change splitAlternating M n (fun i =>
    (if i ∈ S then LinearMap.inl ℂ M M else LinearMap.inr ℂ M M) (v i)) = _
  congr 1
  funext i
  split_ifs <;> rfl

/-- Signed slot permutation is precisely permutation of the actual root assignment. -/
theorem assignmentMap_signedSlot {n : ℕ} (σ : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (x : ⨂[ℂ]^n M) :
    assignmentMap M S (SymmetricFamily.signedSlot M σ x) =
      assignmentMap M (S.map σ.toEmbedding) x := by
  have h : (assignmentMap M S).comp (SymmetricFamily.signedSlot M σ) =
      assignmentMap M (S.map σ.toEmbedding) := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      SymmetricFamily.signedSlot, LinearMap.smul_apply, LinearEquiv.coe_coe,
      SymmetricFamily.slotPermute_tprod, map_smul, assignmentMap_tprod]
    have hv : (fun i => if i ∈ S then ((v ∘ σ) i, (0 : M)) else (0, (v ∘ σ) i)) =
        (fun i => if i ∈ S.map σ.toEmbedding then (v i, (0 : M)) else (0, v i)) ∘ σ := by
      funext i
      simp only [Function.comp_apply]
      have hi : σ i ∈ S.map σ.toEmbedding ↔ i ∈ S := by simp
      rw [if_congr hi rfl rfl]
    rw [hv, (splitAlternating M n).map_perm]
    simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    simp only [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
      Int.cast_one, one_smul]
  exact LinearMap.congr_fun h x

/-- The actual primitive exterior shuffle is the sum of all literal coloring assignments. -/
theorem shuffle_ιMulti_assignments (n : ℕ) (v : Fin n → M) :
    shuffle M (ExteriorAlgebra.ιMulti ℂ n v) =
      ∑ S : Finset (Fin n), assignmentMap M S (PiTensorProduct.tprod ℂ v) := by
  have h := (splitAlternating M n).toMultilinearMap.map_add_univ
    (fun i => (v i, (0 : M))) (fun i => ((0 : M), v i))
  simp only [assignmentMap_tprod]
  have hi : splitAlternating M n (fun i => (v i, v i)) =
      shuffle M (ExteriorAlgebra.ιMulti ℂ n v) := by
    change splitShuffle M (ExteriorAlgebra.ιMulti ℂ n (fun i => (v i, v i))) = _
    rw [← splitShuffle_diagonal M, ExteriorAlgebra.map_apply_ιMulti]
    rfl
  rw [← hi]
  change splitAlternating M n (fun i => (v i + 0, 0 + v i)) =
    ∑ S : Finset (Fin n), splitAlternating M n
      (fun i => if i ∈ S then (v i, 0) else (0, v i)) at h
  simpa only [add_zero, zero_add] using h

end KhanSL2.Factorization.ExteriorShuffle
