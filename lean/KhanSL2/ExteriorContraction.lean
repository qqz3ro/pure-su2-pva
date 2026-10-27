module

public import KhanSL2.ExteriorParity
public import Mathlib.Tactic.Module

@[expose] public section

/-! Odd contractions on the concrete finite exterior algebra. -/

noncomputable section

namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α]

def contraction (code : α → ℕ) (a : α) : Exterior α →ₗ[ℂ] Exterior α :=
  Finsupp.linearCombination ℂ fun s =>
    if a ∈ s then (-1 : ℂ) ^ position code a s • monomial (s.erase a) else 0

@[simp] theorem contraction_monomial (code : α → ℕ) (a : α) (s : Finset α) :
    contraction code a (monomial s) =
      if a ∈ s then (-1 : ℂ) ^ position code a s • monomial (s.erase a) else 0 := by
  simp [contraction, monomial]

@[simp] theorem position_erase_self (code : α → ℕ) (a : α) (s : Finset α) :
    position code a (s.erase a) = position code a s := by
  unfold position
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · exact fun h => ⟨h.1.2, h.2⟩
  · intro h
    exact ⟨⟨fun heq => by subst b; exact Nat.lt_irrefl _ h.2, h.1⟩, h.2⟩

@[simp] theorem position_insert_self (code : α → ℕ) (a : α) (s : Finset α) :
    position code a (insert a s) = position code a s := by
  unfold position
  congr 1
  ext b
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · intro h
    rcases h.1 with rfl | hmem
    · exact (Nat.lt_irrefl _ h.2).elim
    · exact ⟨hmem, h.2⟩
  · exact fun h => ⟨Or.inr h.1, h.2⟩

theorem position_insert (code : α → ℕ) (a b : α) (s : Finset α)
    (hb : b ∉ s) :
    position code a (insert b s) =
      (if code b < code a then 1 else 0) + position code a s := by
  unfold position
  rw [Finset.filter_insert]
  by_cases h : code b < code a
  · simp only [ite_eq_left h]
    rw [Finset.card_insert_of_notMem]
    · omega
    · intro hmem
      exact hb (Finset.mem_filter.mp hmem).1
  · simp [h]

theorem position_erase (code : α → ℕ) (a b : α) (s : Finset α)
    (hb : b ∈ s) :
    position code a s =
      (if code b < code a then 1 else 0) + position code a (s.erase b) := by
  rw [← position_insert code a b (s.erase b) (Finset.notMem_erase b s),
    Finset.insert_erase hb]

theorem contraction_generator_wedge_monomial
    (code : α → ℕ) (hinj : Function.Injective code)
    (a b : α) (s : Finset α) :
    contraction code a (wedge code (generator b) (monomial s)) =
      (if a = b then monomial s else 0) -
        wedge code (generator b) (contraction code a (monomial s)) := by
  by_cases hab : a = b
  · subst b
    by_cases ha : a ∈ s
    · rw [wedge_generator_monomial_of_mem code a s ha, map_zero,
        contraction_monomial, ite_eq_left ha, ite_eq_left rfl,
        wedge_smul_right, wedge_generator_monomial code a (s.erase a)
          (Finset.notMem_erase a s),
        position_erase_self, Finset.insert_erase ha, smul_smul, sign_mul_self, one_smul]
      simp
    · rw [wedge_generator_monomial code a s ha, map_smul, contraction_monomial,
        ite_eq_left (Finset.mem_insert_self a s), position_insert_self,
        Finset.erase_insert ha, smul_smul, sign_mul_self, one_smul,
        contraction_monomial, ite_eq_right ha, ite_eq_left rfl, wedge_zero_right, sub_zero]
  · by_cases hb : b ∈ s
    · rw [wedge_generator_monomial_of_mem code b s hb, map_zero, ite_eq_right hab,
        contraction_monomial]
      by_cases ha : a ∈ s
      · rw [ite_eq_left ha, wedge_smul_right,
          wedge_generator_monomial_of_mem code b (s.erase a)
            (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)]
        simp
      · simp [ha]
    · rw [wedge_generator_monomial code b s hb, map_smul,
        contraction_monomial, ite_eq_right hab, contraction_monomial]
      by_cases ha : a ∈ s
      · have hai : a ∈ insert b s := Finset.mem_insert_of_mem ha
        have hbe : b ∉ s.erase a := fun h => hb (Finset.mem_of_mem_erase h)
        rw [ite_eq_left hai, ite_eq_left ha, wedge_smul_right,
          wedge_generator_monomial code b (s.erase a) hbe,
          Finset.erase_insert_of_ne (Ne.symm hab), zero_sub, smul_smul, smul_smul,
          ← pow_add, ← pow_add]
        have hpa := position_insert code a b s hb
        have hpb := position_erase code b a s ha
        have hne : code a ≠ code b := fun h => hab (hinj h)
        have heq : position code b s + position code a (insert b s) =
            position code a s + position code b (s.erase a) + 1 := by
          by_cases hlt : code a < code b
          · have hgt : ¬ code b < code a := by omega
            simp only [hlt, hgt, ite_eq_left, if_false] at hpa hpb
            omega
          · have hgt : code b < code a := by omega
            simp only [hlt, hgt, ite_eq_left, if_false] at hpa hpb
            omega
        rw [heq, pow_succ, mul_neg_one, neg_smul]
      · have hai : a ∉ insert b s := by simp [hab, ha]
        simp [ha, hai]

theorem contraction_generator_wedge
    (code : α → ℕ) (hinj : Function.Injective code)
    (a b : α) (u : Exterior α) :
    contraction code a (wedge code (generator b) u) =
      (if a = b then u else 0) -
        wedge code (generator b) (contraction code a u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    simp only [wedge_add_right, map_add, hu, hv]
    split <;> module
  | single s r =>
    have hs : Finsupp.single s r = r • monomial s := by simp [monomial]
    rw [hs, wedge_smul_right, map_smul,
      contraction_generator_wedge_monomial code hinj,
      map_smul, wedge_smul_right, smul_sub]
    split <;> simp

/-- The signed removal of a generator is an odd derivation. -/
theorem contraction_wedge
    (code : α → ℕ) (hinj : Function.Injective code)
    (a : α) (u v : Exterior α) :
    contraction code a (wedge code u v) =
      wedge code (contraction code a u) v +
        wedge code (parityLinear u) (contraction code a v) := by
  induction u using induction_on code with
  | hzero => simp
  | hone =>
    simp only [wedge_one_left, contraction_monomial, Finset.notMem_empty,
      if_false, wedge_zero_left, parity_one, zero_add]
  | hadd u w hu hw =>
    simp only [wedge_add_left, map_add, hu, hw, wedge_add_right]
    module
  | hsmul r u hu =>
    simp only [wedge_smul_left, map_smul, hu, smul_add]
  | hgen b u hu =>
    rw [wedge_assoc, contraction_generator_wedge code hinj,
      contraction_generator_wedge code hinj,
      parity_generator_wedge, hu]
    simp only [wedge_add_right, wedge_assoc]
    by_cases hab : a = b
    · simp only [ite_eq_left hab]
      simp only [wedge, map_sub, LinearMap.sub_apply, map_neg, LinearMap.neg_apply]
      simp only [show ∀x y z, wedgeLinear code (wedgeLinear code x y) z =
        wedgeLinear code x (wedgeLinear code y z) from wedge_assoc code]
      module
    · simp only [ite_eq_right hab, zero_sub, wedge_zero_left]
      simp only [wedge, map_neg, LinearMap.neg_apply]
      simp only [show ∀x y z, wedgeLinear code (wedgeLinear code x y) z =
        wedgeLinear code x (wedgeLinear code y z) from wedge_assoc code]
      module

end KhanSL2.FiniteExterior
