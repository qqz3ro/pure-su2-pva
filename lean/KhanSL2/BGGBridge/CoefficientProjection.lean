module

public import KhanSL2.BGGBridge.TrivialCoefficients

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # Projection to a coefficient degree in the actual harmonic windows -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.BGGBridge
open KhanSL2.BGG KhanSL2.Current

/-- Projection to exterior coefficient degree B, in the existing monomial basis. -/
def coefficientProjection (B : ℕ) : Module.End ℂ NB :=
  basisN.constr ℂ fun t => if t.card = B then basisN t else 0

/-- Partial inverse of the coefficient number operator minus B. -/
def coefficientComplementInv (B : ℕ) : Module.End ℂ NB :=
  basisN.constr ℂ fun t => (((t.card : ℂ) - (B : ℂ))⁻¹) • basisN t

/-- Projection plus the inverse on the complementary degrees is identity. -/
theorem coefficientComplementInv_identity (B : ℕ) (ν : NB) :
    coefficientComplementInv B (LieChains.derivExt (1 : Module.End ℂ Cur) ν - (B : ℂ) • ν) +
      coefficientProjection B ν = ν := by
  have h : (coefficientComplementInv B).comp
      (LieChains.derivExt (1 : Module.End ℂ Cur) - (B : ℂ) • LinearMap.id) +
      coefficientProjection B = LinearMap.id := by
    apply basisN.ext
    intro t
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, LieChains.derivExt_one_basis,
      map_sub, map_smul, coefficientComplementInv, coefficientProjection, Module.Basis.constr_basis]
    rw [← sub_smul, smul_smul]
    by_cases ht : t.card = B
    · simp only [ht, sub_self, inv_zero, mul_zero, zero_smul, if_true, zero_add]
    · have hc : (t.card : ℂ) - (B : ℂ) ≠ 0 :=
        sub_ne_zero.mpr (fun he => ht (Nat.cast_inj.mp he))
      rw [mul_inv_cancel₀ hc, one_smul, if_neg ht, add_zero]
  exact LinearMap.congr_fun h ν

/-- The projected coefficient vector has the prescribed exterior degree. -/
theorem coefficientProjection_eigen (B : ℕ) (ν : NB) :
    LieChains.derivExt (1 : Module.End ℂ Cur) (coefficientProjection B ν) =
      (B : ℂ) • coefficientProjection B ν := by
  have h : (LieChains.derivExt (1 : Module.End ℂ Cur)).comp (coefficientProjection B) =
      (B : ℂ) • coefficientProjection B := by
    apply basisN.ext
    intro t
    simp only [LinearMap.comp_apply, LinearMap.smul_apply,
      coefficientProjection, Module.Basis.constr_basis]
    by_cases ht : t.card = B
    · rw [if_pos ht, LieChains.derivExt_one_basis, ht]
    · rw [if_neg ht, map_zero, smul_zero]
  exact LinearMap.congr_fun h ν

/-- A harmonic chain of coefficient degree B is unchanged by the coefficient projection. -/
theorem eq_lTensor_coefficientProjection (B : ℕ) {z : HarmN NB}
    (hz : numBH z = (B : ℂ) • z) :
    z = LinearMap.lTensor PositiveCE.Harmonic (coefficientProjection B) z := by
  have key : ∀ w : HarmN NB,
      LinearMap.lTensor PositiveCE.Harmonic (coefficientComplementInv B)
          (numBH w - (B : ℂ) • w) +
        LinearMap.lTensor PositiveCE.Harmonic (coefficientProjection B) w = w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul h ν =>
      rw [numBH, LinearMap.lTensor_tmul, ← TensorProduct.tmul_smul,
        ← TensorProduct.tmul_sub, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
        ← TensorProduct.tmul_add, coefficientComplementInv_identity]
    | add w w' hw hw' =>
      conv_rhs => rw [← hw, ← hw']
      rw [map_add, smul_add, map_add]
      simp only [map_sub, map_add]
      abel
  have h := key z
  rw [hz, sub_self, map_zero, zero_add] at h
  exact h.symm

/-- It suffices to check a harmonic-window property on tensors of the two prescribed degrees.
No assertion about the polynomial BGG action or projectivity is used. -/
theorem harmWin_le_of_tmul (p B : ℕ) (S : ℤ) (W : Submodule ℂ (HarmN NB))
    (ht : ∀ h : PositiveCE.Harmonic, h ∈ degH p → ∀ ν : NB,
      LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν → h ⊗ₜ[ℂ] ν ∈ W) :
    harmWin p B S ≤ W := by
  intro z hz
  rw [eq_lTensor_coefficientProjection B (Module.End.mem_eigenspace_iff.mp hz.1.2)]
  obtain ⟨y, rfl⟩ := hz.1.1
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul h ν =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, LinearMap.lTensor_tmul]
    exact ht h h.property (coefficientProjection B ν) (coefficientProjection_eigen B ν)
  | add y w hy hw =>
    rw [map_add, map_add]
    exact W.add_mem hy hw

end KhanSL2.BGGBridge
