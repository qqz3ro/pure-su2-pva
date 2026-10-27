module

public import KhanSL2.Macdonald.MixedCoproductPairing
public import KhanSL2.Macdonald.StrongBridgeHomologyRaising

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Nondegeneracy of the actual finite tensor pairing and the genuine colour
projection. These give restriction of the primitive coproduct without assuming
any coalgebra property of the homology equivalence. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

/-- The tensor pairing has the product of the two nonzero factorial norms. -/
theorem tensorSquarePairing_basis_left (b c : BasisIndex) (u : W ⊗[ℂ] W) :
    tensorSquarePairing (basis b ⊗ₜ[ℂ] basis c) u =
      ((exponentFactorial b.1 : ℂ) * (exponentFactorial c.1 : ℂ)) *
        (basis.tensorProduct basis).repr u (b,c) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,Finsupp.add_apply,hu,hv,mul_add]
  | tmul u v =>
    rw [tensorSquarePairing_tmul,pairing_basis_left,pairing_basis_left,
      Module.Basis.tensorProduct_repr_tmul_apply]
    simp only [smul_eq_mul]
    ring

/-- Pure cochain tensors separate every finite chain tensor, without finite-dimensionality. -/
theorem tensorSquarePairing_nondegenerate {z : W ⊗[ℂ] W}
    (h : ∀ u v : W, tensorSquarePairing (u ⊗ₜ[ℂ] v) z = 0) : z = 0 := by
  apply (basis.tensorProduct basis).repr.injective
  ext ⟨b,c⟩
  have hb := h (basis b) (basis c)
  rw [tensorSquarePairing_basis_left] at hb
  have hn : (exponentFactorial b.1 : ℂ) * (exponentFactorial c.1 : ℂ) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (exponentFactorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (exponentFactorial_ne_zero _))
  simpa only [map_zero,Finsupp.zero_apply] using (mul_eq_zero.mp hb).resolve_left hn

theorem tensorSquarePairing_ext {z t : W ⊗[ℂ] W}
    (h : ∀ u v : W, tensorSquarePairing (u ⊗ₜ[ℂ] v) z =
      tensorSquarePairing (u ⊗ₜ[ℂ] v) t) : z = t := by
  apply sub_eq_zero.mp
  apply tensorSquarePairing_nondegenerate
  intro u v
  rw [map_sub,h,sub_self]

theorem strongProjFull_idempotent (u : StrongMacdonald.W) :
    StrongMacdonald.projFull (StrongMacdonald.projFull u) = StrongMacdonald.projFull u := by
  induction u using StrongMacdonald.mono_induction with
  | h0 => simp
  | hadd u v hu hv => simp only [map_add,hu,hv]
  | hsmul c u hu => simp only [map_smul,hu]
  | hmono e t =>
    have hp := StrongMacdonald.proj_mono (fun g : StrongMacdonald.SMode => g.color=0)
      (fun g : Mode => g.color=0) e t
    change StrongMacdonald.projFull (StrongMacdonald.projFull (StrongMacdonald.mono e t)) = _
    change StrongMacdonald.projFull (StrongMacdonald.mono e t) = _ at hp
    by_cases hc : (∀ g ∈ e.support, g.color=0) ∧ (∀ g ∈ t, g.color=0)
    · simp only [hp,if_pos hc]
    · simp only [hp,if_neg hc,map_zero]

/-- The colour-zero projection in the actual polynomial/exterior coordinates. -/
def strongColorProjection : W →ₐ[ℂ] W :=
  strongModelAlg.toAlgHom.comp (StrongMacdonald.projFull.comp strongModelAlg.symm.toAlgHom)

@[simp] theorem strongColorProjection_model (u : StrongMacdonald.W) :
    strongColorProjection (strongModel u) = strongModel (StrongMacdonald.projFull u) := by
  change strongModel (StrongMacdonald.projFull (strongModel.symm (strongModel u))) = _
  rw [strongModel.symm_apply_apply]

theorem strongColorProjection_idempotent (u : W) :
    strongColorProjection (strongColorProjection u) = strongColorProjection u := by
  obtain ⟨v,rfl⟩ := strongModel.surjective u
  rw [strongColorProjection_model,strongColorProjection_model,strongProjFull_idempotent]

/-- The colour projection is diagonal for the original factorial pairing. -/
theorem strongProjFull_pairing (u v : StrongMacdonald.W) :
    pairing (strongModel (StrongMacdonald.projFull u)) (strongModel v) =
      pairing (strongModel u) (strongModel (StrongMacdonald.projFull v)) := by
  induction u using StrongMacdonald.mono_induction with
  | h0 => simp
  | hadd u w hu hw => simp only [map_add,LinearMap.add_apply,hu,hw]
  | hsmul c u hu => simp only [map_smul,LinearMap.smul_apply,hu]
  | hmono e t =>
    have hp := StrongMacdonald.proj_mono (fun g : StrongMacdonald.SMode => g.color=0)
      (fun g : Mode => g.color=0) e t
    change StrongMacdonald.projFull (StrongMacdonald.mono e t) = _ at hp
    rw [hp]
    by_cases hc : (∀ g ∈ e.support, g.color=0) ∧ (∀ g ∈ t, g.color=0)
    · rw [if_pos hc,strongModel_mono,pairing_basis_left,pairing_basis_left,
        basis_repr_strongModel,basis_repr_strongModel]
      rw [StrongMacdonald.projFull,StrongMacdonald.coefW_proj,if_pos hc]
    · rw [if_neg hc,map_zero,map_zero,LinearMap.zero_apply,strongModel_mono,pairing_basis_left,
        basis_repr_strongModel,StrongMacdonald.projFull,StrongMacdonald.coefW_proj,if_neg hc,mul_zero]

theorem strongColorProjection_pairing (u v : W) :
    pairing (strongColorProjection u) v = pairing u (strongColorProjection v) := by
  obtain ⟨a,rfl⟩ := strongModel.surjective u
  obtain ⟨b,rfl⟩ := strongModel.surjective v
  rw [strongColorProjection_model,strongColorProjection_model,strongProjFull_pairing]

theorem tensorSquarePairing_projection (u v : W) (z : W ⊗[ℂ] W) :
    tensorSquarePairing (strongColorProjection u ⊗ₜ[ℂ] strongColorProjection v) z =
      tensorSquarePairing (u ⊗ₜ[ℂ] v)
        (TensorProduct.map strongColorProjection.toLinearMap strongColorProjection.toLinearMap z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simp only [map_add,hz,ht]
  | tmul a b =>
    rw [TensorProduct.map_tmul,tensorSquarePairing_tmul,tensorSquarePairing_tmul,
      strongColorProjection_pairing,strongColorProjection_pairing]
    rfl

/-- The original primitive coproduct respects the actual colour projection. -/
theorem mixedCoproduct_colorProjection (w : W) :
    mixedCoproduct (strongColorProjection w) =
      TensorProduct.map strongColorProjection.toLinearMap strongColorProjection.toLinearMap
        (mixedCoproduct w) := by
  apply tensorSquarePairing_ext
  intro u v
  rw [← tensorSquarePairing_projection,← pairing_mul_mixedCoproduct,
    ← pairing_mul_mixedCoproduct,← map_mul,strongColorProjection_pairing]

end KhanSL2.Macdonald
