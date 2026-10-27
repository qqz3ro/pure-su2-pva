module

public import KhanSL2.BasisGrading

@[expose] public section
noncomputable section
open scoped BigOperators
namespace KhanSL2.BasisGrading
variable {α ι : Type*} [DecidableEq ι] (degree : α → ι)

theorem sum_projection (u : α →₀ ℂ) :
    (∑ i ∈ (coaction degree u).support, projection degree i u) = u := by
  have hs : (coaction degree u).sum (fun _ v => v) = u := by
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv =>
      rw [map_add, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), hu, hv]
    | single a r => simp
  simpa only [Finsupp.sum, coaction_apply] using hs

/-- A kernel calculation on each homogeneous piece implies the global calculation.
Only finitely many homogeneous projections contribute for any input. -/
theorem map_eq_zero_of_ker_piece (F T : Module.End ℂ (α →₀ ℂ))
    (hF : ∀ i u, u ∈ piece degree i → F u ∈ piece degree i)
    (hT : ∀ i u, u ∈ piece degree i → F u = 0 → T u = 0)
    {u : α →₀ ℂ} (hu : F u = 0) : T u = 0 := by
  conv_lhs => rw [← sum_projection degree u]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply hT i _ (projection_mem degree i u)
  have hp := projection_linearMap degree F id Function.injective_id hF i u
  simpa only [id_eq, hu, map_zero] using hp.symm

end KhanSL2.BasisGrading