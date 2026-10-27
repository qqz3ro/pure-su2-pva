module

public import KhanSL2.BGG.PositiveTransferFiltration
public import KhanSL2.BGG.FreeCESquareZero

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual finite homological perturbation transfer from the free CE complex
to U(n) tensored with the proved harmonic representations. No exactness is assumed. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.PositiveTransfer

/-- The unperturbed free bracket boundary squares to zero. -/
theorem baseBoundary_comp_self_zero :
    (PositiveCE.boundary.baseChange PositiveEnveloping).comp
      (PositiveCE.boundary.baseChange PositiveEnveloping) = 0 := by
  rw [baseBoundary_eq_bracket]
  apply LinearMap.ext
  intro u
  exact FreeCE.bracket_square_zero u

/-- The proved actual CE differential is the perturbation of the bracket-only boundary. -/
theorem sourceDifferential_eq : PositiveCE.boundary.baseChange PositiveEnveloping + FreeCE.action =
    FreeCE.differential := by
  rw [baseBoundary_eq_bracket, FreeCE.differential, add_comm]

/-- The perturbation compatibility follows from the actual free CE square-zero theorem. -/
theorem perturbation_square_compat :
    (PositiveCE.boundary.baseChange PositiveEnveloping + FreeCE.action).comp
      (PositiveCE.boundary.baseChange PositiveEnveloping + FreeCE.action) =
    (PositiveCE.boundary.baseChange PositiveEnveloping).comp
      (PositiveCE.boundary.baseChange PositiveEnveloping) := by
  rw [sourceDifferential_eq, baseBoundary_comp_self_zero]
  exact FreeCE.differential_mul_self

/-- The actual pointwise finite perturbation operator. -/
def series : Module.End PositiveEnveloping Chain :=
  baseContraction.perturbationSeries FreeCE.action

/-- An explicit finite series formula, with a bound supplied by exterior energy. -/
theorem series_apply_eq_sum {n : ℕ} {u : Chain} (hu : u ∈ filtration n) :
    series u = ∑ j ∈ Finset.range n,
      ((-(FreeCE.action * baseContraction.homotopy))^j) (FreeCE.action u) := by
  apply baseContraction.perturbationSeries_apply_eq_sum_of_pow_apply_eq_zero FreeCE.action
    isUnit_one_add_action_homotopy
  apply action_homotopy_pow_eq_zero
  exact action_mem_filtration (filtration_mono (Nat.le_succ n) hu)

/-- The transferred differential on the actual harmonic free module. -/
def differential : Module.End PositiveEnveloping HarmonicChain :=
  baseContraction.perturbedDifferential FreeCE.action

/-- The transferred differential is explicitly projection, finite perturbation series, inclusion. -/
theorem differential_apply (u : HarmonicChain) :
    differential u = baseContraction.proj (series (baseContraction.incl u)) := by
  simp only [differential, TauCeti.LinearSpecialContraction.perturbedDifferential_def,
    LinearMap.add_apply, LinearMap.comp_apply, LinearMap.baseChange_zero,
    LinearMap.zero_apply, zero_add, series]

/-- The actual U(n)-linear transferred differential squares to zero. -/
theorem differential_comp_self_zero : differential.comp differential = 0 :=
  baseContraction.perturbedDifferential_comp_perturbedDifferential_eq_zero FreeCE.action
    perturbation_square_compat isUnit_one_add_action_homotopy baseBoundary_comp_self_zero

@[simp] theorem differential_square_zero (u : HarmonicChain) : differential (differential u) = 0 :=
  LinearMap.congr_fun differential_comp_self_zero u

/-- The actual U(n)-linear special contraction after finite perturbation. -/
def contraction : TauCeti.LinearSpecialContraction FreeCE.differential differential :=
  let c := baseContraction.perturb FreeCE.action perturbation_square_compat
    isUnit_one_add_action_homotopy
  { incl := c.incl
    proj := c.proj
    homotopy := c.homotopy
    dM_comp_incl := by simpa only [sourceDifferential_eq, differential] using c.dM_comp_incl
    proj_comp_dM := by simpa only [sourceDifferential_eq, differential] using c.proj_comp_dM
    proj_comp_incl := c.proj_comp_incl
    dM_comp_homotopy_add_homotopy_comp_dM := by
      simpa only [sourceDifferential_eq] using c.dM_comp_homotopy_add_homotopy_comp_dM
    homotopy_comp_incl := c.homotopy_comp_incl
    proj_comp_homotopy := c.proj_comp_homotopy
    homotopy_comp_homotopy := c.homotopy_comp_homotopy }
/-- The transferred complex is a deformation retract of the actual free CE complex. -/
theorem contraction_identity (u : Chain) :
    FreeCE.differential (contraction.homotopy u) + contraction.homotopy (FreeCE.differential u) =
      u - contraction.incl (contraction.proj u) :=
  LinearMap.congr_fun contraction.dM_comp_homotopy_add_homotopy_comp_dM u

end KhanSL2.BGG.PositiveTransfer
