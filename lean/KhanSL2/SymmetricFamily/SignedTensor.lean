module

public import KhanSL2.SymmetricFamily.WordInvariants
public import KhanSL2.PolynomialBGG.ProjectiveModelDeriv

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The generic normalized exterior power is precisely the signed invariant
part of the actual labelled tensor power. No current-color choice is involved. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

variable (M : Type*) [AddCommGroup M] [Module ℂ M]

/-- Actual precomposition of the labelled tensor slots. -/
def slotPermute {k : ℕ} (σ : Equiv.Perm (Fin k)) : (⨂[ℂ]^k M) ≃ₗ[ℂ] (⨂[ℂ]^k M) :=
  PiTensorProduct.reindex ℂ (fun _ : Fin k => M) σ.symm

@[simp] theorem slotPermute_tprod {k : ℕ} (σ : Equiv.Perm (Fin k)) (v : Fin k → M) :
    slotPermute M σ (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (v ∘ σ) := by
  simp [slotPermute, PiTensorProduct.reindex_tprod, Function.comp_def]

theorem slotPermute_comp {k : ℕ} (σ τ : Equiv.Perm (Fin k)) (x : ⨂[ℂ]^k M) :
    slotPermute M τ (slotPermute M σ x) = slotPermute M (σ*τ) x := by
  have h : (slotPermute M τ).toLinearMap.comp (slotPermute M σ).toLinearMap =
      (slotPermute M (σ*τ)).toLinearMap := by
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro v
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, slotPermute_tprod, Function.comp_def, Equiv.Perm.coe_mul]
  exact LinearMap.congr_fun h x

/-- Multiply the actual slot permutation by its sign. -/
def signedSlot {k : ℕ} (σ : Equiv.Perm (Fin k)) : Module.End ℂ (⨂[ℂ]^k M) :=
  (σ.sign : ℂ) • (slotPermute M σ).toLinearMap

theorem signedSlot_comp {k : ℕ} (σ τ : Equiv.Perm (Fin k)) (x : ⨂[ℂ]^k M) :
    signedSlot M τ (signedSlot M σ x) = signedSlot M (σ*τ) x := by
  simp only [signedSlot, LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul,
    slotPermute_comp, smul_smul]
  congr 1
  simp only [map_mul, Units.val_mul, Int.cast_mul]

/-- Signed invariant labelled tensors. -/
def signedInvariantTensors (k : ℕ) : Submodule ℂ (⨂[ℂ]^k M) where
  carrier := {x | ∀ σ : Equiv.Perm (Fin k), signedSlot M σ x = x}
  zero_mem' := by simp
  add_mem' hx hy σ := by rw [map_add, hx σ, hy σ]
  smul_mem' c _ hx σ := by rw [map_smul, hx σ]

/-- Signed averaging, with the explicit invertible factorial normalization. -/
def signedAverage (k : ℕ) : Module.End ℂ (⨂[ℂ]^k M) :=
  (Fintype.card (Equiv.Perm (Fin k)) : ℂ)⁻¹ • ∑ σ : Equiv.Perm (Fin k), signedSlot M σ

theorem signedAverage_mem (k : ℕ) (x : ⨂[ℂ]^k M) :
    signedAverage M k x ∈ signedInvariantTensors M k := by
  intro τ
  simp only [signedAverage, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
    map_sum, signedSlot_comp]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ => signedSlot M σ x)

theorem signedAverage_eq_self {k : ℕ} {x : ⨂[ℂ]^k M}
    (hx : x ∈ signedInvariantTensors M k) : signedAverage M k x = x := by
  change ∀ σ, signedSlot M σ x = x at hx
  simp only [signedAverage, LinearMap.smul_apply, LinearMap.sum_apply, hx,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (permutationCard_ne_zero k), one_smul]

/-- The normalized alternating quotient-section composite is exactly signed averaging. -/
theorem alternatingProjection_eq_signedAverage (k : ℕ) :
    (exteriorToTensor M k).comp (tensorToExterior M k) = signedAverage M k := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    tensorToExterior_tprod, exteriorToTensor, LinearMap.smul_apply,
    exteriorPower.toTensorPower_apply_ιMulti, signedAverage, LinearMap.sum_apply,
    signedSlot, LinearMap.smul_apply, LinearEquiv.coe_coe, slotPermute_tprod,
    Fintype.card_perm, Fintype.card_fin]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, Function.comp_def]

/-- The existing normalized exterior section lands in actual signed tensor invariants. -/
theorem exteriorToTensor_mem_signed (k : ℕ) (x : ⋀[ℂ]^k M) :
    exteriorToTensor M k x ∈ signedInvariantTensors M k := by
  have h : signedAverage M k (exteriorToTensor M k x) = exteriorToTensor M k x := by
    rw [← alternatingProjection_eq_signedAverage, LinearMap.comp_apply]
    rw [show tensorToExterior M k (exteriorToTensor M k x) = x from
      LinearMap.congr_fun (tensorToExterior_exteriorToTensor M k) x]
  rw [← h]
  exact signedAverage_mem M k _

/-- Genuine exterior-power / signed-invariant tensor equivalence. -/
def exteriorSignedTensorEquiv (k : ℕ) : (⋀[ℂ]^k M) ≃ₗ[ℂ] signedInvariantTensors M k where
  toFun x := ⟨exteriorToTensor M k x, exteriorToTensor_mem_signed M k x⟩
  invFun x := tensorToExterior M k x.val
  left_inv x := LinearMap.congr_fun (tensorToExterior_exteriorToTensor M k) x
  right_inv x := by
    apply Subtype.ext
    change exteriorToTensor M k (tensorToExterior M k x.val) = x.val
    exact (LinearMap.congr_fun (alternatingProjection_eq_signedAverage M k) x.val).trans
      (signedAverage_eq_self M x.property)
  map_add' x y := by apply Subtype.ext; exact map_add (exteriorToTensor M k) x y
  map_smul' c x := by apply Subtype.ext; exact map_smul (exteriorToTensor M k) c x

/-- The signed comparison intertwines every actual induced derivation. -/
theorem exteriorSignedTensorEquiv_deriv (k : ℕ) (D : Module.End ℂ M) (x : ⋀[ℂ]^k M) :
    (exteriorSignedTensorEquiv M k (exteriorDeriv k D x)).val =
      tensorDeriv k D (exteriorSignedTensorEquiv M k x).val :=
  LinearMap.congr_fun (exteriorToTensor_exteriorDeriv k D) x

end KhanSL2.SymmetricFamily
