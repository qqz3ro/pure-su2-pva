module

public import KhanSL2.SymmetricFamily.CurrentTensorBlocks
public import KhanSL2.SymmetricFamily.SignedTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The original normalized alternating section commutes with restriction to
two literal tensor blocks. All signs arise from the actual slot permutations. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

variable (M : Type*) [AddCommGroup M] [Module ℂ M]

theorem tensorSlotsBlockEquiv_permute (r s : ℕ) (σ : Equiv.Perm (Fin r))
    (τ : Equiv.Perm (Fin s)) (x : ⨂[ℂ]^(r+s) M) :
    tensorSlotsBlockEquiv M r s (slotPermute M (blockPermutationHom r s (σ,τ)) x) =
      TensorProduct.map (slotPermute M σ).toLinearMap (slotPermute M τ).toLinearMap
        (tensorSlotsBlockEquiv M r s x) := by
  have he : (tensorSlotsBlockEquiv M r s).toLinearMap.comp
      (slotPermute M (blockPermutationHom r s (σ,τ))).toLinearMap =
      (TensorProduct.map (slotPermute M σ).toLinearMap (slotPermute M τ).toLinearMap).comp
        (tensorSlotsBlockEquiv M r s).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply,LinearMap.comp_apply,LinearEquiv.coe_coe,
      slotPermute_tprod,tensorSlotsBlockEquiv_tprod,TensorProduct.map_tmul]
    apply congrArg₂ (fun (u : ⨂[ℂ]^r M) (w : ⨂[ℂ]^s M) => u ⊗ₜ[ℂ] w)
    · apply congrArg (PiTensorProduct.tprod ℂ)
      funext i
      exact congrArg v (blockPermutation_castAdd r s (σ,τ) i)
    · apply congrArg (PiTensorProduct.tprod ℂ)
      funext i
      exact congrArg v (blockPermutation_natAdd r s (σ,τ) i)
  exact LinearMap.congr_fun he x

theorem tensorSlotsBlockEquiv_signed (r s : ℕ) (σ : Equiv.Perm (Fin r))
    (τ : Equiv.Perm (Fin s)) (x : ⨂[ℂ]^(r+s) M) :
    tensorSlotsBlockEquiv M r s (signedSlot M (blockPermutationHom r s (σ,τ)) x) =
      TensorProduct.map (signedSlot M σ) (signedSlot M τ)
        (tensorSlotsBlockEquiv M r s x) := by
  rw [signedSlot,LinearMap.smul_apply,map_smul]
  simp only [LinearEquiv.coe_coe]
  rw [tensorSlotsBlockEquiv_permute]
  simp only [signedSlot,TensorProduct.map_smul_left,TensorProduct.map_smul_right,
    LinearMap.smul_apply,smul_smul,blockPermutation_sign,Units.val_mul,Int.cast_mul,mul_comm]

theorem tensorSlotsBlock_signedAverage (r s : ℕ) (x : ⨂[ℂ]^(r+s) M)
    (hx : x ∈ signedInvariantTensors M (r+s)) :
    TensorProduct.map (signedAverage M r) (signedAverage M s)
      (tensorSlotsBlockEquiv M r s x) = tensorSlotsBlockEquiv M r s x := by
  have ha : TensorProduct.map (signedAverage M r) (signedAverage M s) =
      (Fintype.card (Equiv.Perm (Fin r)) : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin r),
      (Fintype.card (Equiv.Perm (Fin s)) : ℂ)⁻¹ • ∑ τ : Equiv.Perm (Fin s),
        TensorProduct.map (signedSlot M σ) (signedSlot M τ) := by
    change TensorProduct.mapBilinear (RingHom.id ℂ) (⨂[ℂ]^r M) (⨂[ℂ]^s M)
      (⨂[ℂ]^r M) (⨂[ℂ]^s M) (signedAverage M r) (signedAverage M s) = _
    simp only [signedAverage,map_smul,map_sum,LinearMap.smul_apply,LinearMap.sum_apply,
      TensorProduct.mapBilinear_apply]
    simp_rw [← Finset.smul_sum]
    rw [smul_comm,Finset.sum_comm]
  have hf (σ : Equiv.Perm (Fin r)) (τ : Equiv.Perm (Fin s)) :
      TensorProduct.map (signedSlot M σ) (signedSlot M τ)
        (tensorSlotsBlockEquiv M r s x) = tensorSlotsBlockEquiv M r s x := by
    rw [← tensorSlotsBlockEquiv_signed,hx]
  rw [ha]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,hf,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (permutationCard_ne_zero r),one_smul,
    ← Nat.cast_smul_eq_nsmul ℂ,smul_smul,inv_mul_cancel₀ (permutationCard_ne_zero s),one_smul]

/-- Wedge the two literal blocks of the original normalized alternating section. -/
def exteriorTensorBlock (r s : ℕ) : (⋀[ℂ]^(r+s) M) →ₗ[ℂ]
    (⋀[ℂ]^r M) ⊗[ℂ] (⋀[ℂ]^s M) :=
  (TensorProduct.map (tensorToExterior M r) (tensorToExterior M s)).comp
    ((tensorSlotsBlockEquiv M r s).toLinearMap.comp (exteriorToTensor M (r+s)))

/-- The separate normalized sections recover the literal two-block alternating tensor. -/
theorem exteriorTensorBlock_section (r s : ℕ) (p : ⋀[ℂ]^(r+s) M) :
    TensorProduct.map (exteriorToTensor M r) (exteriorToTensor M s)
      (exteriorTensorBlock M r s p) =
        tensorSlotsBlockEquiv M r s (exteriorToTensor M (r+s) p) := by
  change TensorProduct.map (exteriorToTensor M r) (exteriorToTensor M s)
    (TensorProduct.map (tensorToExterior M r) (tensorToExterior M s)
      (tensorSlotsBlockEquiv M r s (exteriorToTensor M (r+s) p))) = _
  rw [TensorProduct.map_map,alternatingProjection_eq_signedAverage,alternatingProjection_eq_signedAverage]
  exact tensorSlotsBlock_signedAverage M r s _ (exteriorToTensor_mem_signed M (r+s) p)

end KhanSL2.SymmetricFamily
