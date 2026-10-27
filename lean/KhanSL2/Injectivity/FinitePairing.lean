module

public import KhanSL2.ExteriorRing
public import KhanSL2.ExteriorContraction

/-! The algebraic coefficient pairing on finite exterior chains and cochains.
Left multiplication by a generator and odd contraction are adjoint. -/

@[expose] public section

noncomputable section

namespace KhanSL2.FiniteExterior

variable {α : Type*}

def coefficientPairing : Exterior α →ₗ[ℂ] Exterior α →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ fun s => Finsupp.lapply s

@[simp] theorem coefficientPairing_single (s : Finset α) (z : ℂ) (u : Exterior α) :
    coefficientPairing (Finsupp.single s z) u = z * u s := by
  simp [coefficientPairing]

@[simp] theorem coefficientPairing_monomial (s : Finset α) (u : Exterior α) :
    coefficientPairing (monomial s) u = u s := by
  simp [monomial]

theorem coefficientPairing_symm (u v : Exterior α) :
    coefficientPairing u v = coefficientPairing v u := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw]
  | single s a =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add, LinearMap.add_apply, hv, hw]
    | single t b =>
      by_cases h : s = t
      · subst t
        simp [mul_comm]
      · simp [Finsupp.single_apply, h, Ne.symm h]

@[simp] theorem coefficientPairing_monomial_right (u : Exterior α) (s : Finset α) :
    coefficientPairing u (monomial s) = u s := by
  rw [coefficientPairing_symm, coefficientPairing_monomial]

variable [DecidableEq α] [GeneratorOrder α]

theorem coefficientPairing_generator_monomial (a : α) (s t : Finset α) :
    coefficientPairing (generator a * monomial s) (monomial t) =
      coefficientPairing (monomial s) (contraction GeneratorOrder.code a (monomial t)) := by
  change coefficientPairing (wedge GeneratorOrder.code (generator a) (monomial s)) _ = _
  rw [coefficientPairing_monomial, contraction_monomial]
  by_cases ha : a ∈ s
  · rw [wedge_generator_monomial_of_mem _ _ _ ha]
    by_cases hat : a ∈ t
    · have he : t.erase a ≠ s := by
        intro h
        have := Finset.notMem_erase a t
        exact this (h.symm ▸ ha)
      simp [contraction_monomial, hat, monomial, Finsupp.single_apply, he]
    · simp [contraction_monomial, hat]
  · rw [wedge_generator_monomial _ _ _ ha]
    by_cases ht : t = insert a s
    · subst t
      simp [contraction_monomial, position_insert_self, Finset.erase_insert ha, monomial]
    · by_cases hat : a ∈ t
      · have he : t.erase a ≠ s := by
          intro h
          apply ht
          rw [← Finset.insert_erase hat, h]
        simp [contraction_monomial, hat, monomial, Finsupp.single_apply,
          ht, Ne.symm ht, he]
      · simp [contraction_monomial, hat, monomial, Finsupp.single_apply, ht, Ne.symm ht]

theorem coefficientPairing_generator_mul (a : α) (u v : Exterior α) :
    coefficientPairing (generator a * u) v =
      coefficientPairing u (contraction GeneratorOrder.code a v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u w hu hw => simp only [mul_add, map_add, LinearMap.add_apply, hu, hw]
  | single s r =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw => simp only [map_add, hv, hw]
    | single t z =>
      have hr : Finsupp.single s r = r • monomial s := by simp [monomial]
      have hz : Finsupp.single t z = z • monomial t := by simp [monomial]
      rw [hr, hz, mul_smul_comm]
      simp only [map_smul, LinearMap.smul_apply, coefficientPairing_generator_monomial]

theorem coefficientPairing_contraction (a : α) (u v : Exterior α) :
    coefficientPairing (contraction GeneratorOrder.code a u) v =
      coefficientPairing u (generator a * v) := by
  rw [coefficientPairing_symm, ← coefficientPairing_generator_mul, coefficientPairing_symm]

@[simp] theorem coefficientPairing_one_generator_mul (a : α) (u : Exterior α) :
    coefficientPairing 1 (generator a * u) = 0 := by
  rw [coefficientPairing_symm, coefficientPairing_generator_mul]
  change coefficientPairing u (contraction GeneratorOrder.code a (monomial ∅)) = 0
  simp

end KhanSL2.FiniteExterior
