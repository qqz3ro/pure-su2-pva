module

public import KhanSL2.ExteriorAlgebra

@[expose] public section

/-! The finite permutation counts controlling exterior signs. -/

noncomputable section

namespace KhanSL2.FiniteExterior

variable {α : Type*} [DecidableEq α]

def position (code : α → ℕ) (a : α) (s : Finset α) : ℕ :=
  (s.filter fun b => code b < code a).card

def afterCount (code : α → ℕ) (a : α) (s : Finset α) : ℕ :=
  (s.filter fun b => code a < code b).card

omit [DecidableEq α] in
@[simp] theorem inversionCount_singleton_left (code : α → ℕ) (a : α) (s : Finset α) :
    inversionCount code {a} s = position code a s := by
  simp [inversionCount, position]

theorem inversionCount_insert_left (code : α → ℕ) (a : α) (s t : Finset α)
    (ha : a ∉ s) :
    inversionCount code (insert a s) t =
      position code a t + inversionCount code s t := by
  simp [inversionCount, position, Finset.sum_insert, ha]

theorem inversionCount_erase_left (code : α → ℕ) (a : α) (s t : Finset α)
    (ha : a ∈ s) :
    inversionCount code s t =
      position code a t + inversionCount code (s.erase a) t := by
  rw [← inversionCount_insert_left code a (s.erase a) t (Finset.notMem_erase a s),
    Finset.insert_erase ha]

omit [DecidableEq α] in
@[simp] theorem inversionCount_singleton_right (code : α → ℕ) (a : α) (s : Finset α) :
    inversionCount code s {a} = afterCount code a s := by
  simp only [inversionCount, afterCount]
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.filter_singleton]
  by_cases h : code a < code b <;> simp [h]

theorem inversionCount_insert_right (code : α → ℕ) (a : α) (s t : Finset α)
    (ha : a ∉ t) :
    inversionCount code s (insert a t) =
      afterCount code a s + inversionCount code s t := by
  rw [Finset.insert_eq, inversionCount_union_right]
  · rw [inversionCount_singleton_right]
  · simpa using ha

theorem inversionCount_erase_right (code : α → ℕ) (a : α) (s t : Finset α)
    (ha : a ∈ t) :
    inversionCount code s t =
      afterCount code a s + inversionCount code s (t.erase a) := by
  rw [← inversionCount_insert_right code a s (t.erase a) (Finset.notMem_erase a t),
    Finset.insert_erase ha]

omit [DecidableEq α] in
theorem position_add_afterCount (code : α → ℕ) (hinj : Function.Injective code)
    (a : α) (s : Finset α) (ha : a ∉ s) :
    position code a s + afterCount code a s = s.card := by
  unfold position afterCount
  have heq : s.filter (fun b => code a < code b) =
      s.filter (fun b => ¬ code b < code a) := by
    apply Finset.filter_congr
    intro b hb
    have hne : code b ≠ code a := fun h => ha (hinj h ▸ hb)
    omega
  rw [heq, Finset.card_filter_add_card_filter_not]

theorem position_union (code : α → ℕ) (a : α) (s t : Finset α)
    (hst : Disjoint s t) :
    position code a (s ∪ t) = position code a s + position code a t := by
  unfold position
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact hst.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem inversionCount_swap (code : α → ℕ) (hinj : Function.Injective code)
    (s t : Finset α) (hst : Disjoint s t) :
    inversionCount code s t + inversionCount code t s = s.card * t.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hst' : Disjoint s t := (Finset.disjoint_insert_left.mp hst).2
    have hat : a ∉ t := (Finset.disjoint_insert_left.mp hst).1
    rw [inversionCount_insert_left code a s t ha,
      inversionCount_insert_right code a t s ha, Finset.card_insert_of_notMem ha]
    have hcount := position_add_afterCount code hinj a t hat
    have hi := ih hst'
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem sign_mul_self (n : ℕ) : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
  rw [← mul_pow]
  simp

theorem monomialWedge_supercomm (code : α → ℕ) (hinj : Function.Injective code)
    (s t : Finset α) :
    monomialWedge code s t =
      (-1 : ℂ) ^ (s.card * t.card) • monomialWedge code t s := by
  by_cases hst : Disjoint s t
  · have hts := hst.symm
    simp only [monomialWedge, hst, hts, ↓reduceIte, Finsupp.smul_single, smul_eq_mul]
    rw [Finset.union_comm t s, ← inversionCount_swap code hinj s t hst,
      pow_add, mul_assoc, sign_mul_self, mul_one]
  · have hts : ¬Disjoint t s := fun h => hst h.symm
    simp [monomialWedge, hst, hts]

theorem wedge_monomial_supercomm (code : α → ℕ) (hinj : Function.Injective code)
    (s t : Finset α) :
    wedge code (monomial s) (monomial t) =
      (-1 : ℂ) ^ (s.card * t.card) • wedge code (monomial t) (monomial s) := by
  simpa using monomialWedge_supercomm code hinj s t

theorem wedge_generator_monomial (code : α → ℕ) (a : α) (s : Finset α)
    (ha : a ∉ s) :
    wedge code (generator a) (monomial s) =
      (-1 : ℂ) ^ position code a s • monomial (insert a s) := by
  simp [generator, monomialWedge, ha, monomial]

theorem wedge_generator_monomial_of_mem (code : α → ℕ) (a : α) (s : Finset α)
    (ha : a ∈ s) :
    wedge code (generator a) (monomial s) = 0 := by
  simp [generator, monomialWedge, ha]

theorem wedge_generator_monomial_eq (code : α → ℕ) (a : α) (s : Finset α) :
    wedge code (generator a) (monomial s) =
      if a ∈ s then 0 else
        (-1 : ℂ) ^ position code a s • monomial (insert a s) := by
  by_cases ha : a ∈ s
  · simp [ha, wedge_generator_monomial_of_mem code a s ha]
  · simp [ha, wedge_generator_monomial code a s ha]

theorem monomial_insert (code : α → ℕ) (a : α) (s : Finset α)
    (ha : a ∉ s) :
    monomial (insert a s) =
      (-1 : ℂ) ^ position code a s • wedge code (generator a) (monomial s) := by
  rw [wedge_generator_monomial code a s ha, smul_smul, sign_mul_self, one_smul]

theorem induction_on (code : α → ℕ) {P : Exterior α → Prop}
    (hzero : P 0) (hone : P (monomial ∅))
    (hadd : ∀u v, P u → P v → P (u + v))
    (hsmul : ∀(r : ℂ) u, P u → P (r • u))
    (hgen : ∀a u, P u → P (wedge code (generator a) u))
    (u : Exterior α) : P u := by
  induction u using Finsupp.induction_linear with
  | zero => exact hzero
  | add u v hu hv => exact hadd u v hu hv
  | single s r =>
    have hs : P (monomial s) := by
      induction s using Finset.induction_on with
      | empty => exact hone
      | @insert a s ha ih =>
        rw [monomial_insert code a s ha]
        exact hsmul _ _ (hgen _ _ ih)
    simpa [monomial] using hsmul r (monomial s) hs

end KhanSL2.FiniteExterior
