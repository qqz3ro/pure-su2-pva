module

public import KhanSL2.SymmetricFamily.ExteriorTensorSection
public import KhanSL2.Factorization.ExteriorBlockTensor

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The canonical power-valued alternating coproduct is the actual signed
shuffle lift, with its precise factorial/binomial normalization. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization.ExteriorBlock

variable (M : Type*) [AddCommGroup M] [Module ℂ M]

/-- Wedge the literal blocks into the original exterior powers. -/
def tensorExteriorPowerBlock (r s : ℕ) : (⨂[ℂ]^(r+s) M) →ₗ[ℂ]
    (⋀[ℂ]^r M) ⊗[ℂ] (⋀[ℂ]^s M) :=
  (TensorProduct.map (tensorToExterior M r) (tensorToExterior M s)).comp
    (tensorSlotsBlockEquiv M r s).toLinearMap

@[simp] theorem tensorExteriorPowerBlock_tprod (r s : ℕ) (v : Fin (r+s) → M) :
    tensorExteriorPowerBlock M r s (PiTensorProduct.tprod ℂ v) =
      exteriorPower.ιMulti ℂ r (fun i => v (Fin.castAdd s i)) ⊗ₜ[ℂ]
        exteriorPower.ιMulti ℂ s (fun i => v (Fin.natAdd r i)) := by
  simp only [tensorExteriorPowerBlock,LinearMap.comp_apply,LinearEquiv.coe_coe,
    tensorSlotsBlockEquiv_tprod,TensorProduct.map_tmul,tensorToExterior_tprod,Function.comp_def]

/-- The canonical homogeneous component of the original alternating coproduct. -/
def exteriorPowerCoproductComponent (r s : ℕ) : (⋀[ℂ]^(r+s) M) →ₗ[ℂ]
    (⋀[ℂ]^r M) ⊗[ℂ] (⋀[ℂ]^s M) :=
  exteriorPower.alternatingMapLinearEquiv (R:=ℂ) (M:=M) (n:=r+s)
    (N := (⋀[ℂ]^r M) ⊗[ℂ] (⋀[ℂ]^s M))
    (((exteriorPower.ιMulti ℂ r (M:=M)).domCoprod (exteriorPower.ιMulti ℂ s (M:=M))).domDomCongr
      finSumFinEquiv)

@[simp] theorem exteriorPowerCoproductComponent_ιMulti (r s : ℕ) (v : Fin (r+s) → M) :
    exteriorPowerCoproductComponent M r s (exteriorPower.ιMulti ℂ (r+s) v) =
      ((exteriorPower.ιMulti ℂ r).domCoprod (exteriorPower.ιMulti ℂ s))
        (v ∘ finSumFinEquiv) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The original normalized section gives exactly the inverse-binomial signed shuffle component. -/
theorem exteriorTensorBlock_eq_inv_choose (r s : ℕ) (x : ⋀[ℂ]^(r+s) M) :
    exteriorTensorBlock M r s x =
      (Nat.choose (r+s) r : ℂ)⁻¹ • exteriorPowerCoproductComponent M r s x := by
  have heq : (tensorExteriorPowerBlock M r s).compMultilinearMap (PiTensorProduct.tprod ℂ) =
      (MultilinearMap.domCoprod (exteriorPower.ιMulti ℂ r (M:=M)).toMultilinearMap
        (exteriorPower.ιMulti ℂ s (M:=M)).toMultilinearMap).domDomCongr finSumFinEquiv := by
    ext v
    exact tensorExteriorPowerBlock_tprod M r s v
  have h := LinearMap.compMultilinearMap_alternatization
    (N' := ⨂[ℂ]^(r+s) M) (N'₂ := (⋀[ℂ]^r M) ⊗[ℂ] (⋀[ℂ]^s M))
    (tensorExteriorPowerBlock M r s) (PiTensorProduct.tprod ℂ)
  rw [heq,alternatization_domDomCongr,
    MultilinearMap.domCoprod_alternatization_eq] at h
  have hmap : (tensorExteriorPowerBlock M r s).comp (exteriorToTensor M (r+s)) =
      (Nat.choose (r+s) r : ℂ)⁻¹ • exteriorPowerCoproductComponent M r s := by
    apply exteriorPower.linearMap_ext (N := (⋀[ℂ]^r M) ⊗[ℂ] (⋀[ℂ]^s M))
    apply AlternatingMap.ext
    intro v
    have hv := congrArg (fun f => f v) h
    simp only [AlternatingMap.domDomCongr_apply,AlternatingMap.smul_apply,
      Fintype.card_fin,LinearMap.compAlternatingMap_apply] at hv
    change tensorExteriorPowerBlock M r s (exteriorToTensor M (r+s)
      (exteriorPower.ιMulti ℂ (r+s) v)) = _
    rw [exteriorToTensor,LinearMap.smul_apply,map_smul]
    simp only [exteriorPower.toTensorPower,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rw [← hv,← Nat.cast_smul_eq_nsmul ℂ,smul_smul,Nat.cast_mul,factorial_ratio_eq_inv_choose]
    simp only [LinearMap.compAlternatingMap_apply,LinearMap.smul_apply,
      exteriorPowerCoproductComponent_ιMulti]
  exact LinearMap.congr_fun hmap x

/-- The canonical component has the exact binomial normalization, including zero-sized blocks. -/
theorem exteriorPowerCoproductComponent_tensorBlock (r s : ℕ) (x : ⋀[ℂ]^(r+s) M) :
    exteriorPowerCoproductComponent M r s x =
      (Nat.choose (r+s) r : ℂ) • exteriorTensorBlock M r s x := by
  rw [exteriorTensorBlock_eq_inv_choose,smul_smul,mul_inv_cancel₀ (block_choose_ne_zero r s),one_smul]

end KhanSL2.SymmetricFamily
