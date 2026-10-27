module

public import KhanSL2.BGG.PositiveTransfer
public import KhanSL2.BGG.PositiveTransferDegreeBase

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
namespace KhanSL2.BGG.PositiveTransfer

/-- Each term of the actual finite perturbation series lowers exterior degree by one. -/
theorem series_mem_degree {p : ℕ} {u : Chain} (hu : u ∈ sourceDegree (p+1)) :
    series u ∈ sourceDegree p := by
  obtain ⟨n, hn⟩ := filtration_exhaustive u
  rw [series_apply_eq_sum hn]
  apply (sourceDegree p).sum_mem
  intro j hjmem
  clear hjmem
  induction j with
  | zero => simpa only [pow_zero, Module.End.one_apply] using action_mem_degree hu
  | succ j hj =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, Module.End.mul_apply]
    exact (sourceDegree p).neg_mem (action_mem_degree (base_homotopy_mem_degree hj))

/-- The actual perturbation series vanishes in exterior degree zero. -/
theorem series_eq_zero_of_degree_zero {u : Chain} (hu : u ∈ sourceDegree 0) : series u = 0 := by
  rw [series, TauCeti.LinearSpecialContraction.perturbationSeries_def, Module.End.mul_apply,
    action_eq_zero_of_degree_zero hu, map_zero]

/-- The transferred differential has precisely homological degree minus one. -/
theorem differential_mem_degree {p : ℕ} {u : HarmonicChain}
    (hu : u ∈ harmonicTensorDegree (p+1)) : differential u ∈ harmonicTensorDegree p := by
  rw [differential_apply]
  exact base_proj_mem_degree (series_mem_degree (base_incl_mem_degree hu))

/-- The transferred differential vanishes on the actual zeroth chain group. -/
theorem differential_eq_zero_of_degree_zero {u : HarmonicChain}
    (hu : u ∈ harmonicTensorDegree 0) : differential u = 0 := by
  rw [differential_apply, series_eq_zero_of_degree_zero (base_incl_mem_degree hu), map_zero]

theorem contraction_incl_apply (u : HarmonicChain) :
    contraction.incl u = baseContraction.incl u -
      baseContraction.homotopy (series (baseContraction.incl u)) := by
  change (baseContraction.perturb FreeCE.action perturbation_square_compat
    isUnit_one_add_action_homotopy).incl u = _
  rw [TauCeti.LinearSpecialContraction.perturb_incl]
  rfl

theorem contraction_proj_apply (u : Chain) :
    contraction.proj u = baseContraction.proj u -
      baseContraction.proj (series (baseContraction.homotopy u)) := by
  change (baseContraction.perturb FreeCE.action perturbation_square_compat
    isUnit_one_add_action_homotopy).proj u = _
  rw [TauCeti.LinearSpecialContraction.perturb_proj]
  rfl

theorem contraction_homotopy_apply (u : Chain) :
    contraction.homotopy u = baseContraction.homotopy u -
      baseContraction.homotopy (series (baseContraction.homotopy u)) := by
  change (baseContraction.perturb FreeCE.action perturbation_square_compat
    isUnit_one_add_action_homotopy).homotopy u = _
  rw [TauCeti.LinearSpecialContraction.perturb_homotopy]
  rfl

/-- The perturbed inclusion preserves actual exterior degree. -/
theorem contraction_incl_mem_degree {p : ℕ} {u : HarmonicChain}
    (hu : u ∈ harmonicTensorDegree p) : contraction.incl u ∈ sourceDegree p := by
  rw [contraction_incl_apply]
  cases p with
  | zero =>
    rw [series_eq_zero_of_degree_zero (base_incl_mem_degree hu), map_zero, sub_zero]
    exact base_incl_mem_degree hu
  | succ p =>
    exact (sourceDegree (p+1)).sub_mem (base_incl_mem_degree hu)
      (base_homotopy_mem_degree (series_mem_degree (base_incl_mem_degree hu)))

/-- The perturbed projection preserves actual exterior degree. -/
theorem contraction_proj_mem_degree {p : ℕ} {u : Chain} (hu : u ∈ sourceDegree p) :
    contraction.proj u ∈ harmonicTensorDegree p := by
  rw [contraction_proj_apply]
  exact (harmonicTensorDegree p).sub_mem (base_proj_mem_degree hu)
    (base_proj_mem_degree (series_mem_degree (base_homotopy_mem_degree hu)))

/-- The perturbed homotopy still raises actual exterior degree by one. -/
theorem contraction_homotopy_mem_degree {p : ℕ} {u : Chain} (hu : u ∈ sourceDegree p) :
    contraction.homotopy u ∈ sourceDegree (p+1) := by
  rw [contraction_homotopy_apply]
  exact (sourceDegree (p+1)).sub_mem (base_homotopy_mem_degree hu)
    (base_homotopy_mem_degree (series_mem_degree (base_homotopy_mem_degree hu)))

end KhanSL2.BGG.PositiveTransfer
