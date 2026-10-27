module

public import KhanSL2.SymmetricFamily.SignedTensor
public import KhanSL2.SymmetricFamily.CurrentSlots

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! The actual exterior current coefficients are the signed simultaneous
invariants in labelled-root polynomials with finite current-color tensors. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

/-- The simultaneous root/color permutation with its alternating sign. -/
def signedLabelledPermute {k : ℕ} (σ : Equiv.Perm (Fin k)) : Module.End ℂ (Labelled k) :=
  (σ.sign : ℂ) • labelledPermute σ

/-- Actual signed labelled-root invariants. -/
def signedInvariantLabelled (k : ℕ) : Submodule ℂ (Labelled k) where
  carrier := {x | ∀ σ : Equiv.Perm (Fin k), signedLabelledPermute σ x = x}
  zero_mem' := by simp
  add_mem' hx hy σ := by rw [map_add, hx σ, hy σ]
  smul_mem' c _ hx σ := by rw [map_smul, hx σ]

theorem rootTensorEquiv_signedSlot {k : ℕ} (σ : Equiv.Perm (Fin k))
    (x : ⨂[ℂ]^k BGG.Current) :
    rootTensorEquiv k (signedSlot BGG.Current σ x) =
      signedLabelledPermute σ (rootTensorEquiv k x) := by
  change rootTensorEquiv k ((σ.sign : ℂ) • tensorPermute σ x) = _
  rw [map_smul, rootTensorEquiv_permute]
  rfl

/-- The actual labelled-root comparison restricts to signed tensor invariants. -/
def signedTensorLabelledEquiv (k : ℕ) :
    signedInvariantTensors BGG.Current k ≃ₗ[ℂ] signedInvariantLabelled k where
  toFun x := ⟨rootTensorEquiv k x.val, by
    intro σ
    rw [← rootTensorEquiv_signedSlot, x.property σ]⟩
  invFun x := ⟨(rootTensorEquiv k).symm x.val, by
    intro σ
    apply (rootTensorEquiv k).injective
    rw [rootTensorEquiv_signedSlot, LinearEquiv.apply_symm_apply]
    exact x.property σ⟩
  left_inv x := by
    apply Subtype.ext
    exact (rootTensorEquiv k).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    exact (rootTensorEquiv k).apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact map_add (rootTensorEquiv k) x.val y.val
  map_smul' c x := by apply Subtype.ext; exact map_smul (rootTensorEquiv k) c x.val

/-- The genuine exterior-power / signed labelled-root equivalence. -/
def exteriorLabelledEquiv (k : ℕ) :
    (⋀[ℂ]^k BGG.Current) ≃ₗ[ℂ] signedInvariantLabelled k :=
  (exteriorSignedTensorEquiv BGG.Current k).trans (signedTensorLabelledEquiv k)

/-- The original raising coefficient operator is root power-sum multiplication. -/
theorem exteriorLabelledEquiv_coefficientEnd (m k : ℕ) (x : ⋀[ℂ]^k BGG.Current) :
    (exteriorLabelledEquiv k (exteriorDeriv k (Modules.coefficientShift m) x)).val =
      LinearMap.rTensor (Color k)
        (LinearMap.mulLeft ℂ (show RootPolynomial k from MvPolynomial.psum (Fin k) ℂ m))
        (exteriorLabelledEquiv k x).val := by
  change rootTensorEquiv k (exteriorToTensor BGG.Current k
    (exteriorDeriv k (Modules.coefficientShift m) x)) = _
  have h := LinearMap.congr_fun (exteriorToTensor_exteriorDeriv k (Modules.coefficientShift m)) x
  simp only [LinearMap.comp_apply] at h
  exact (congrArg (rootTensorEquiv k) h).trans (rootTensorEquiv_coefficientShift m k _)

/-- The full original current action is the sum of the labelled evaluation actions. -/
theorem exteriorLabelledEquiv_mode_lie (k n : ℕ) (a : BGG.G) (x : ⋀[ℂ]^k BGG.Current) :
    (exteriorLabelledEquiv k
      (exteriorDeriv k (LieAlgebra.ad ℂ BGG.Current (BGG.mode n a)) x)).val =
      labelledModeEnd k n (LieAlgebra.ad ℂ BGG.G a)
        (exteriorLabelledEquiv k x).val := by
  change rootTensorEquiv k (exteriorToTensor BGG.Current k
    (exteriorDeriv k (LieAlgebra.ad ℂ BGG.Current (BGG.mode n a)) x)) = _
  have h := LinearMap.congr_fun
    (exteriorToTensor_exteriorDeriv k (LieAlgebra.ad ℂ BGG.Current (BGG.mode n a))) x
  simp only [LinearMap.comp_apply] at h
  apply (congrArg (rootTensorEquiv k) h).trans
  rw [ad_mode_eq_modeColorEnd]
  exact rootTensorEquiv_modeColorEnd k n _ _

end KhanSL2.SymmetricFamily
