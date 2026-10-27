module

public import KhanSL2.BGG.FreeCESupport

@[expose] public section
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE
open PositiveCE FiniteExterior

/-- The specified free CE boundary squares to zero on each pure tensor. The finite
commutator correction is cancelled by the mixed action/bracket anticommutator. -/
theorem differential_square_zero_tmul (u : PositiveEnveloping) (ω : Cochain) :
    differential (differential (u ⊗ₜ[ℂ] ω)) = 0 := by
  let S := supportModes ω
  let T := bracketSupport S
  have hS : supportModes ω ⊆ S := Finset.Subset.refl _
  have hST : S ⊆ T := subset_bracketSupport S
  have hm : ∀ m∈S, ∀ n∈S, ∀ a : Fin 3, mergeMode m n a∈T :=
    mergeMode_mem_bracketSupport S
  have hA : action (u ⊗ₜ[ℂ] ω) = finiteAction S (u ⊗ₜ[ℂ] ω) :=
    (finiteAction_tmul_eq S u ω hS).symm
  have hAT : action (u ⊗ₜ[ℂ] ω) = finiteAction T (u ⊗ₜ[ℂ] ω) :=
    (finiteAction_tmul_eq T u ω (hS.trans hST)).symm
  have hAA : action (action (u ⊗ₜ[ℂ] ω)) =
      (1/2:ℂ) • coefficientCorrection S u ω := by
    rw [hA, action_finiteAction S u ω hS, finiteAction_square]
  have hAB : action (bracket (u ⊗ₜ[ℂ] ω)) =
      finiteAction T (finiteBracket S (u ⊗ₜ[ℂ] ω)) := by
    rw [bracket_tmul, finiteBracket_tmul, finiteBoundary_eq S ω hS]
    exact (finiteAction_tmul_eq T u _
      (supportModes_boundary_subset S T hST hm ω hS)).symm
  have hBA : bracket (action (u ⊗ₜ[ℂ] ω)) =
      finiteBracket S (finiteAction T (u ⊗ₜ[ℂ] ω)) := by
    rw [hAT, bracket_finiteAction S T u ω hS]
  have hmix : action (bracket (u ⊗ₜ[ℂ] ω)) + bracket (action (u ⊗ₜ[ℂ] ω)) =
      -(1/2:ℂ) • coefficientCorrection S u ω := by
    rw [hAB, hBA, finiteAction_bracket S T hm]
  change action (action (u ⊗ₜ[ℂ] ω) + bracket (u ⊗ₜ[ℂ] ω)) +
    bracket (action (u ⊗ₜ[ℂ] ω) + bracket (u ⊗ₜ[ℂ] ω)) = 0
  rw [map_add, map_add, bracket_square_zero, add_zero]
  calc
    _ = action (action (u ⊗ₜ[ℂ] ω)) +
        (action (bracket (u ⊗ₜ[ℂ] ω)) + bracket (action (u ⊗ₜ[ℂ] ω))) := by abel
    _ = (1/2:ℂ) • coefficientCorrection S u ω +
        -(1/2:ℂ) • coefficientCorrection S u ω := by rw [hAA, hmix]
    _ = 0 := by module

/-- The actual free Chevalley--Eilenberg differential squares to zero. -/
@[simp] theorem differential_square_zero (t : Chain) : differential (differential t) = 0 := by
  induction t using TensorProduct.inductionOn with
  | tmul u ω => exact differential_square_zero_tmul u ω
  | add t s ht hs => simp only [map_add, ht, hs, add_zero]

theorem differential_mul_self : differential * differential = 0 := by
  apply LinearMap.ext
  intro t
  exact differential_square_zero t

end KhanSL2.BGG.FreeCE