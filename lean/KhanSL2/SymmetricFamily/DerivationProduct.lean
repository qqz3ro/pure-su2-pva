module

public import KhanSL2.Macdonald.CurrentAction

@[expose] public section

/-! The finite product rule for polynomial derivations, including empty products. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.SymmetricFamily

/-- A derivation of a commutative algebra differentiates one factor at a time. -/
theorem derivation_prod {ι R A : Type*} [DecidableEq ι]
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (s : Finset ι) (v : ι → A) :
    D (∏ i ∈ s, v i) = ∑ i ∈ s, D (v i) * ∏ j ∈ s.erase i, v j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha,
      Finset.erase_insert ha]
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact mul_comm _ _
    · apply Finset.sum_congr rfl
      intro i hi
      have hai : a ≠ i := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hai,
        Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring

/-- Equivalent product rule expressed by replacing the differentiated slot. -/
theorem derivation_prod_update {ι R A : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (v : ι → A) :
    D (∏ i, v i) = ∑ i, ∏ j, Function.update v i (D (v i)) j := by
  rw [derivation_prod]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]

end KhanSL2.SymmetricFamily
