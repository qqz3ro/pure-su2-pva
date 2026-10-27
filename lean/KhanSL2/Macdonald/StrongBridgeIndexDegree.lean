module

public import KhanSL2.Macdonald.StrongBridgeRootModel

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual coefficient degree and exterior degree of the root-model indices. -/
noncomputable section
namespace KhanSL2.Macdonald

@[simp] theorem strongFreeEvenEquiv_degree
    (e : {e : StrongMacdonald.Exp // ∀ g ∈ e.support, g.color = 0}) :
    (strongFreeEvenEquiv e).degree = e.val.degree := by
  change (Finsupp.equivMapDomain strongZeroEvenEquiv
    (e.val.subtypeDomain (fun g : StrongMacdonald.SMode => g.color = 0))).sum
      (fun _ n => n) = e.val.sum (fun _ n => n)
  rw [Finsupp.sum_equivMapDomain]
  exact Finsupp.sum_subtypeDomain_index (h := fun (_ : StrongMacdonald.SMode) (n : ℕ) => n) e.property

@[simp] theorem strongFreeOddEquiv_card
    (t : {t : Finset Mode // ∀ m ∈ t, m.color = 0}) :
    (strongFreeOddEquiv t).card = t.val.card := by
  change ((t.val.subtype (fun m : Mode => m.color = 0)).map
    strongZeroOddEquiv.toEmbedding).card = t.val.card
  rw [Finset.card_map, Finset.card_subtype, Finset.filter_eq_self.mpr t.property]

@[simp] theorem strongFreeIndexEquiv_even_degree (b : strongFreeIndices) :
    (strongFreeIndexEquiv b).1.degree = b.val.1.degree :=
  strongFreeEvenEquiv_degree ⟨b.val.1,b.property.1⟩

@[simp] theorem strongFreeIndexEquiv_odd_card (b : strongFreeIndices) :
    (strongFreeIndexEquiv b).2.card = b.val.2.card :=
  strongFreeOddEquiv_card ⟨b.val.2,b.property.2⟩

/-- A root block with q odd and r even generators has actual coefficient degree 2r+q. -/
theorem strongFreeIndex_coefficientDegree (b : strongFreeIndices) :
    StrongMacdonald.diagVal (fun _ => 2) (fun _ => 1) b.val.1 b.val.2 =
      2 * (strongFreeIndexEquiv b).1.degree + (strongFreeIndexEquiv b).2.card := by
  rw [strongFreeIndexEquiv_even_degree, strongFreeIndexEquiv_odd_card]
  simp only [StrongMacdonald.diagVal, Finsupp.sum, Finsupp.degree, Finset.sum_const,
    smul_eq_mul, mul_one]
  rw [← Finset.sum_mul]
  exact congrArg (fun n : ℕ => n + b.val.2.card) (Nat.mul_comm _ _)

/-- The exterior grading is the number of odd root variables. -/
theorem strongFreeIndex_exteriorDegree (b : strongFreeIndices) :
    StrongMacdonald.diagVal (fun _ => 0) (fun _ => 1) b.val.1 b.val.2 =
      (strongFreeIndexEquiv b).2.card := by
  rw [strongFreeIndexEquiv_odd_card]
  simp [StrongMacdonald.diagVal]

end KhanSL2.Macdonald
