module

public import KhanSL2.Factorization.ShuffleExterior
public import Mathlib.LinearAlgebra.Alternating.DomCoprod
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-! # Exact normalization of an alternating two-block map

The normalized full alternation of the tensor product of two alternating maps
is the inverse binomial factor times their signed shuffle product. This result
retains the actual factorial normalization, including either zero block size.
-/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization.ExteriorBlock

variable {M N₁ N₂ : Type*}
  [AddCommGroup M] [Module ℂ M]
  [AddCommGroup N₁] [Module ℂ N₁]
  [AddCommGroup N₂] [Module ℂ N₂]

/-- Full signed alternation of the actual tensor block map, divided by the total factorial. -/
def normalizedDomCoprod {r s : ℕ}
    (a : M [⋀^Fin r]→ₗ[ℂ] N₁) (b : M [⋀^Fin s]→ₗ[ℂ] N₂) :
    M [⋀^(Fin r ⊕ Fin s)]→ₗ[ℂ] (N₁ ⊗[ℂ] N₂) :=
  ((Nat.factorial (r+s) : ℂ)⁻¹) •
    MultilinearMap.alternatization (MultilinearMap.domCoprod a b)

theorem block_choose_ne_zero (r s : ℕ) : (Nat.choose (r+s) r : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos (Nat.le_add_right r s)))

/-- The precise scalar relating factorial-normalized alternation and signed shuffles. -/
theorem factorial_ratio_eq_inv_choose (r s : ℕ) :
    (Nat.factorial (r+s) : ℂ)⁻¹ * ((Nat.factorial r : ℂ) * (Nat.factorial s : ℂ)) =
      (Nat.choose (r+s) r : ℂ)⁻¹ := by
  have hf : (Nat.factorial (r+s) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc : (Nat.choose (r+s) r : ℂ) *
      ((Nat.factorial r : ℂ) * (Nat.factorial s : ℂ)) = (Nat.factorial (r+s) : ℂ) := by
    have hn := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right r s)
    rw [Nat.add_sub_cancel_left] at hn
    exact_mod_cast (by simpa only [Nat.mul_assoc] using hn)
  apply mul_left_cancel₀ (block_choose_ne_zero r s)
  calc
    (Nat.choose (r+s) r : ℂ) *
        ((Nat.factorial (r+s) : ℂ)⁻¹ *
          ((Nat.factorial r : ℂ) * (Nat.factorial s : ℂ))) =
        (Nat.factorial (r+s) : ℂ)⁻¹ *
          ((Nat.choose (r+s) r : ℂ) *
            ((Nat.factorial r : ℂ) * (Nat.factorial s : ℂ))) := by ring
    _ = 1 := by rw [hc, inv_mul_cancel₀ hf]
    _ = (Nat.choose (r+s) r : ℂ) * (Nat.choose (r+s) r : ℂ)⁻¹ :=
      (mul_inv_cancel₀ (block_choose_ne_zero r s)).symm

/-- No unspecified scalar occurs: the normalized block map is exactly inverse-choose times shuffle. -/
theorem normalizedDomCoprod_eq {r s : ℕ}
    (a : M [⋀^Fin r]→ₗ[ℂ] N₁) (b : M [⋀^Fin s]→ₗ[ℂ] N₂) :
    normalizedDomCoprod a b = (Nat.choose (r+s) r : ℂ)⁻¹ • a.domCoprod b := by
  rw [normalizedDomCoprod, MultilinearMap.domCoprod_alternatization_eq]
  simp only [Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_mul, smul_smul]
  rw [factorial_ratio_eq_inv_choose]

theorem domCoprod_eq_choose_smul_normalized {r s : ℕ}
    (a : M [⋀^Fin r]→ₗ[ℂ] N₁) (b : M [⋀^Fin s]→ₗ[ℂ] N₂) :
    a.domCoprod b = (Nat.choose (r+s) r : ℂ) • normalizedDomCoprod a b := by
  rw [normalizedDomCoprod_eq, smul_smul,
    mul_inv_cancel₀ (block_choose_ne_zero r s), one_smul]

/-- The formula for actual exterior block words, with arbitrary vectors as their slots. -/
theorem exterior_normalizedDomCoprod (r s : ℕ) (v : Fin r ⊕ Fin s → M) :
    normalizedDomCoprod (ExteriorAlgebra.ιMulti ℂ r) (ExteriorAlgebra.ιMulti ℂ s) v =
      (Nat.choose (r+s) r : ℂ)⁻¹ •
        ((ExteriorAlgebra.ιMulti ℂ r).domCoprod (ExteriorAlgebra.ιMulti ℂ s)) v := by
  rw [normalizedDomCoprod_eq, AlternatingMap.smul_apply]

end KhanSL2.Factorization.ExteriorBlock
