module

public import KhanSL2.Injectivity.FinitePairing

/-! Support subspaces of the concrete finite exterior algebra. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace KhanSL2.FiniteExterior

variable {α : Type*}

def supportedOn (P : Finset α → Prop) : Submodule ℂ (Exterior α) :=
  Finsupp.supported ℂ ℂ {s | P s}

theorem mem_supportedOn (P : Finset α → Prop) (u : Exterior α) :
    u ∈ supportedOn P ↔ ∀ s ∈ u.support, P s := Iff.rfl

theorem monomial_mem_supportedOn (P : Finset α → Prop) (s : Finset α) (hs : P s) :
    monomial s ∈ supportedOn P :=
  Finsupp.single_mem_supported ℂ 1 hs

theorem eq_sum_support (u : Exterior α) :
    u = ∑ s ∈ u.support, u s • monomial s := by
  simpa only [Finsupp.sum, monomial, Finsupp.smul_single, smul_eq_mul, mul_one]
    using (Finsupp.sum_single u).symm

theorem coefficientPairing_eq_zero_of_support
    (P Q : Finset α → Prop) (hPQ : ∀ s, P s → Q s → False)
    {u v : Exterior α} (hu : u ∈ supportedOn P) (hv : v ∈ supportedOn Q) :
    coefficientPairing u v = 0 := by
  classical
  rw [eq_sum_support u]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    coefficientPairing_monomial]
  apply Finset.sum_eq_zero
  intro s hs
  have hz : v s = 0 := by
    by_contra h
    exact hPQ s ((mem_supportedOn P u).mp hu s hs)
      ((mem_supportedOn Q v).mp hv s (Finsupp.mem_support_iff.mpr h))
  simp [hz]

variable [DecidableEq α] [GeneratorOrder α]

theorem supportedOn_mul (P Q R : Finset α → Prop)
    (hunion : ∀ s t, P s → Q t → R (s ∪ t))
    {u v : Exterior α} (hu : u ∈ supportedOn P) (hv : v ∈ supportedOn Q) :
    u * v ∈ supportedOn R := by
  rw [eq_sum_support u]
  simp only [Finset.sum_mul, smul_mul_assoc]
  apply Submodule.sum_mem
  intro s hs
  apply Submodule.smul_mem
  rw [eq_sum_support v]
  simp only [Finset.mul_sum, mul_smul_comm]
  apply Submodule.sum_mem
  intro t ht
  apply Submodule.smul_mem
  change wedge GeneratorOrder.code (monomial s) (monomial t) ∈ supportedOn R
  rw [wedge_monomial, monomialWedge]
  split
  · exact Finsupp.single_mem_supported ℂ _
      (hunion s t ((mem_supportedOn P u).mp hu s hs)
        ((mem_supportedOn Q v).mp hv t ht))
  · exact (supportedOn R).zero_mem

/-- All modes occurring in each nonzero basis coefficient belong to `S`. -/
def generatorsIn (S : Set α) : Submodule ℂ (Exterior α) :=
  supportedOn (fun s => ∀ a ∈ s, a ∈ S)

omit [DecidableEq α] [GeneratorOrder α] in
theorem monomial_mem_generatorsIn (S : Set α) (s : Finset α)
    (hs : ∀ a ∈ s, a ∈ S) : monomial s ∈ generatorsIn S :=
  monomial_mem_supportedOn _ _ hs

omit [DecidableEq α] [GeneratorOrder α] in
theorem generator_mem_generatorsIn (S : Set α) (a : α) (ha : a ∈ S) :
    generator a ∈ generatorsIn S := by
  apply monomial_mem_generatorsIn
  simpa using ha

theorem one_mem_generatorsIn (S : Set α) : (1 : Exterior α) ∈ generatorsIn S :=
  monomial_mem_generatorsIn S ∅ (by simp)

theorem mul_mem_generatorsIn (S : Set α) {u v : Exterior α}
    (hu : u ∈ generatorsIn S) (hv : v ∈ generatorsIn S) :
    u * v ∈ generatorsIn S := by
  apply supportedOn_mul _ _ _ _ hu hv
  intro s t hs ht a ha
  rcases Finset.mem_union.mp ha with h | h
  · exact hs a h
  · exact ht a h

theorem contraction_mem_generatorsIn (S : Set α) (a : α) {u : Exterior α}
    (hu : u ∈ generatorsIn S) :
    contraction GeneratorOrder.code a u ∈ generatorsIn S := by
  rw [eq_sum_support u]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro s hs
  apply Submodule.smul_mem
  rw [contraction_monomial]
  split
  · apply Submodule.smul_mem
    apply monomial_mem_generatorsIn
    intro b hb
    exact hu hs b (Finset.mem_of_mem_erase hb)
  · exact (generatorsIn S).zero_mem

end KhanSL2.FiniteExterior
