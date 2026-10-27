module

public import KhanSL2.BGG.FreeCEBasis
public import KhanSL2.BGG.EnvelopingGrading
public import KhanSL2.BGG.Induced

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual free Chevalley--Eilenberg boundary over positive currents. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE

open PositiveCE FiniteExterior

abbrev Chain := PositiveEnveloping ⊗[ℂ] Cochain

/-- The actual enveloping generator of one compact-color positive current. -/
def ueGenerator (m : Mode) : PositiveEnveloping := UniversalEnvelopingAlgebra.ι ℂ (lieGenerator m)

/-- One action summand. Multiplication is on the right, so this map is left U(n)-linear. -/
def actionTerm (m : Mode) : Module.End PositiveEnveloping Chain :=
  Induced.tensorLift ((TensorProduct.mk ℂ PositiveEnveloping Cochain (ueGenerator m)).comp (contract m))

@[simp] theorem actionTerm_tmul (m : Mode) (u : PositiveEnveloping) (ω : Cochain) :
    actionTerm m (u ⊗ₜ[ℂ] ω) = (u * ueGenerator m) ⊗ₜ[ℂ] contract m ω := by
  rw [actionTerm, Induced.tensorLift_tmul]
  rfl

/-- A finite cutoff of the action boundary. -/
def finiteAction (S : Finset Mode) : Module.End PositiveEnveloping Chain := ∑ m ∈ S, actionTerm m

@[simp] theorem finiteAction_tmul (S : Finset Mode) (u : PositiveEnveloping) (ω : Cochain) :
    finiteAction S (u ⊗ₜ[ℂ] ω) = ∑ m ∈ S, (u * ueGenerator m) ⊗ₜ[ℂ] contract m ω := by
  simp only [finiteAction, LinearMap.sum_apply, actionTerm_tmul]

/-- Finite exterior support defines the action coefficient map without any infinite sums. -/
def actionCoefficient : Cochain →ₗ[ℂ] Chain :=
  Finsupp.linearCombination ℂ fun s => ∑ m ∈ s, ueGenerator m ⊗ₜ[ℂ] contract m (monomial s)

@[simp] theorem actionCoefficient_monomial (s : Finset Mode) :
    actionCoefficient (monomial s) = ∑ m ∈ s, ueGenerator m ⊗ₜ[ℂ] contract m (monomial s) := by
  simp [actionCoefficient, monomial]

/-- The action part of the standard CE boundary, on the actual free enveloping module. -/
def action : Module.End PositiveEnveloping Chain := Induced.tensorLift actionCoefficient

@[simp] theorem action_tmul (u : PositiveEnveloping) (ω : Cochain) :
    action (u ⊗ₜ[ℂ] ω) = u • actionCoefficient ω := Induced.tensorLift_tmul _ _ _

theorem action_tmul_monomial (u : PositiveEnveloping) (s : Finset Mode) :
    action (u ⊗ₜ[ℂ] monomial s) = ∑ m ∈ s, (u * ueGenerator m) ⊗ₜ[ℂ] contract m (monomial s) := by
  rw [action_tmul, actionCoefficient_monomial]
  simp only [Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul]

/-- A cutoff containing the exterior support computes the action boundary exactly. -/
theorem finiteAction_tmul_monomial (S s : Finset Mode) (hs : s ⊆ S) (u : PositiveEnveloping) :
    finiteAction S (u ⊗ₜ[ℂ] monomial s) = action (u ⊗ₜ[ℂ] monomial s) := by
  rw [finiteAction_tmul, action_tmul_monomial]
  symm
  apply Finset.sum_subset hs
  intro m _ hm
  simp only [contract, contraction_monomial, if_neg hm, TensorProduct.tmul_zero]

theorem finiteAction_tmul_eq (S : Finset Mode) (u : PositiveEnveloping) (ω : Cochain)
    (hω : supportModes ω ⊆ S) : finiteAction S (u ⊗ₜ[ℂ] ω) = action (u ⊗ₜ[ℂ] ω) := by
  rw [eq_sum_support ω]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_smul, LinearMap.map_smul_of_tower]
  apply Finset.sum_congr rfl
  intro s hs
  rw [finiteAction_tmul_monomial S s ((subset_supportModes hs).trans hω)]

/-- The bracket-only boundary tensored with the enveloping algebra. -/
def bracket : Module.End PositiveEnveloping Chain :=
  Induced.tensorLift ((TensorProduct.mk ℂ PositiveEnveloping Cochain 1).comp boundary)

@[simp] theorem bracket_tmul (u : PositiveEnveloping) (ω : Cochain) :
    bracket (u ⊗ₜ[ℂ] ω) = u ⊗ₜ[ℂ] boundary ω := by
  rw [bracket, Induced.tensorLift_tmul]
  change (u * 1) ⊗ₜ[ℂ] boundary ω = _
  rw [mul_one]

/-- The standard free Chevalley--Eilenberg differential is action plus bracket. -/
def differential : Module.End PositiveEnveloping Chain := action + bracket

@[simp] theorem differential_tmul (u : PositiveEnveloping) (ω : Cochain) :
    differential (u ⊗ₜ[ℂ] ω) = action (u ⊗ₜ[ℂ] ω) + u ⊗ₜ[ℂ] boundary ω := by
  simp only [differential, LinearMap.add_apply, bracket_tmul]

theorem differential_tmul_finite (S : Finset Mode) (u : PositiveEnveloping) (ω : Cochain)
    (hω : supportModes ω ⊆ S) :
    differential (u ⊗ₜ[ℂ] ω) =
      (∑ m ∈ S, (u * ueGenerator m) ⊗ₜ[ℂ] contract m ω) + u ⊗ₜ[ℂ] boundary ω := by
  rw [differential_tmul, ← finiteAction_tmul_eq S u ω hω, finiteAction_tmul]

@[simp] theorem action_tmul_one (u : PositiveEnveloping) : action (u ⊗ₜ[ℂ] 1) = 0 := by
  change action (u ⊗ₜ[ℂ] monomial ∅) = 0
  simp only [action_tmul_monomial, Finset.sum_empty]

@[simp] theorem differential_tmul_one (u : PositiveEnveloping) :
    differential (u ⊗ₜ[ℂ] 1) = 0 := by
  simp only [differential_tmul, action_tmul_one, boundary_one, TensorProduct.tmul_zero, add_zero]

@[simp] theorem action_tmul_generator (u : PositiveEnveloping) (m : Mode) :
    action (u ⊗ₜ[ℂ] FiniteExterior.generator m) = (u * ueGenerator m) ⊗ₜ[ℂ] 1 := by
  change action (u ⊗ₜ[ℂ] monomial {m}) = _
  rw [action_tmul_monomial, Finset.sum_singleton]
  change (u * ueGenerator m) ⊗ₜ[ℂ] contract m (FiniteExterior.generator m) = _
  rw [contract_generator, if_pos rfl]

@[simp] theorem differential_tmul_generator (u : PositiveEnveloping) (m : Mode) :
    differential (u ⊗ₜ[ℂ] FiniteExterior.generator m) = (u * ueGenerator m) ⊗ₜ[ℂ] 1 := by
  simp only [differential_tmul, action_tmul_generator, boundary_generator,
    TensorProduct.tmul_zero, add_zero]

end KhanSL2.BGG.FreeCE
