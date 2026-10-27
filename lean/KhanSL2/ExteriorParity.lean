module

public import KhanSL2.ExteriorSigns

@[expose] public section

/-! Parity on the finite exterior algebra. -/

noncomputable section

namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α]

def parityLinear : Exterior α →ₗ[ℂ] Exterior α :=
  Finsupp.linearCombination ℂ fun s => (-1 : ℂ) ^ s.card • monomial s

omit [DecidableEq α] in
@[simp] theorem parity_single (s : Finset α) (r : ℂ) :
    parityLinear (Finsupp.single s r) = (-1 : ℂ) ^ s.card • Finsupp.single s r := by
  simp [parityLinear, monomial, smul_smul, mul_comm]

omit [DecidableEq α] in
@[simp] theorem parity_monomial (s : Finset α) :
    parityLinear (monomial s) = (-1 : ℂ) ^ s.card • monomial s := by
  simp [monomial]

omit [DecidableEq α] in
@[simp] theorem parity_generator (a : α) :
    parityLinear (generator a) = - generator a := by
  simp [generator]

omit [DecidableEq α] in
@[simp] theorem parity_one :
    parityLinear (monomial (∅ : Finset α)) = monomial ∅ := by simp

omit [DecidableEq α] in
@[simp] theorem parity_involutive (u : Exterior α) :
    parityLinear (parityLinear u) = u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single s r => simp [smul_smul, ← mul_assoc, sign_mul_self]

theorem parity_monomialWedge (code : α → ℕ) (s t : Finset α) :
    parityLinear (monomialWedge code s t) =
      (-1 : ℂ) ^ (s.card + t.card) • monomialWedge code s t := by
  by_cases hst : Disjoint s t
  · simp [monomialWedge, hst, Finset.card_union_of_disjoint hst]
  · simp [monomialWedge, hst]

theorem parity_wedge (code : α → ℕ) (u v : Exterior α) :
    parityLinear (wedge code u v) = wedge code (parityLinear u) (parityLinear v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [wedge_add_left, map_add, hu, hv]
  | single s a =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simp only [wedge_add_right, map_add, hu, hv]
    | single t b =>
      simp only [wedge_single, map_smul, parity_single, wedge_smul_left,
        wedge_smul_right, parity_monomialWedge, smul_smul, pow_add]
      congr 1
      ac_rfl

theorem parity_generator_wedge (code : α → ℕ) (a : α) (u : Exterior α) :
    parityLinear (wedge code (generator a) u) =
      -wedge code (generator a) (parityLinear u) := by
  rw [parity_wedge, parity_generator]
  change wedgeLinear code (-generator a) (parityLinear u) = _
  simp [wedge]

end KhanSL2.FiniteExterior
