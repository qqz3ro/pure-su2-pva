module

public import KhanSL2.BGG.FreeCEEquivarianceAction
public import KhanSL2.BGG.FreeCEEquivarianceContraction
public import Mathlib.Tactic.LinearCombination

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Actual constant-sl₂ equivariance of the standard free CE differential. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace KhanSL2.BGG.FreeCE
open PositiveCE FiniteExterior
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem epsilon_symmetric_tensor_sum (a : Fin 3)
    (f : Fin 3 → PositiveEnveloping) (g : Fin 3 → Cochain) :
    (∑ b : Fin 3, ∑ c : Fin 3, KhanSL2.epsilon a b c •
      (f c ⊗ₜ[ℂ] g b + f b ⊗ₜ[ℂ] g c)) = 0 := by
  fin_cases a <;> norm_num [Fin.sum_univ_succ, KhanSL2.epsilon]

/-- A finite all-color cutoff of the action boundary is already constant-equivariant. -/
theorem finiteAction_constantAction_color_tmul (N : ℕ) (a : Fin 3)
    (u : PositiveEnveloping) (ω : Cochain) :
    constantAction (MatrixSL2.color a) (finiteAction (modesBelow N) (u ⊗ₜ[ℂ] ω)) =
      finiteAction (modesBelow N) (constantAction (MatrixSL2.color a) (u ⊗ₜ[ℂ] ω)) := by
  have hz : (∑ i∈Finset.range N, ∑ b : Fin 3, ∑ c : Fin 3, KhanSL2.epsilon a b c •
      ((u * ueGenerator (⟨i,c⟩ : Mode)) ⊗ₜ[ℂ] contract (⟨i,b⟩ : Mode) ω +
       (u * ueGenerator (⟨i,b⟩ : Mode)) ⊗ₜ[ℂ] contract (⟨i,c⟩ : Mode) ω)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact epsilon_symmetric_tensor_sum a
      (fun c => u * ueGenerator (⟨i,c⟩ : Mode)) (fun b => contract (⟨i,b⟩ : Mode) ω)
  simp only [smul_add, Finset.sum_add_distrib] at hz
  simp only [finiteAction_tmul, map_sum, constantAction_color_tmul, map_add,
    positiveUEAction_mul, positiveUEAction_generator_color, colorAction_contract,
    Finset.mul_sum, mul_smul_comm, TensorProduct.add_tmul, TensorProduct.tmul_add,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum, ← TensorProduct.smul_tmul',
    TensorProduct.tmul_smul, Finset.sum_add_distrib, sum_modesBelow]
  abel_nf at hz ⊢
  rw [← add_assoc, hz, zero_add]

/-- The actual action boundary commutes with each constant color action. -/
theorem action_constantAction_color (a : Fin 3) (z : Chain) :
    action (constantAction (MatrixSL2.color a) z) = constantAction (MatrixSL2.color a) (action z) := by
  have hpure (u : PositiveEnveloping) (ω : Cochain) :
      action (constantAction (MatrixSL2.color a) (u ⊗ₜ[ℂ] ω)) =
        constantAction (MatrixSL2.color a) (action (u ⊗ₜ[ℂ] ω)) := by
    let S := supportModes ω ∪ supportModes (PositiveCE.colorAction a ω)
    let N := S.sup PositiveCE.Mode.index + 1
    have hbound (m : Mode) (hm : m∈S) : m∈modesBelow N := by
      rw [mem_modesBelow]
      have h : m.index ≤ S.sup PositiveCE.Mode.index := Finset.le_sup (f := PositiveCE.Mode.index) hm
      change m.index < S.sup PositiveCE.Mode.index + 1
      omega
    have hω : supportModes ω ⊆ modesBelow N := fun m hm => hbound m (Finset.mem_union_left _ hm)
    have hL : supportModes (PositiveCE.colorAction a ω) ⊆ modesBelow N :=
      fun m hm => hbound m (Finset.mem_union_right _ hm)
    rw [← finiteAction_tmul_eq (modesBelow N) u ω hω,
      constantAction_color_tmul, map_add,
      ← finiteAction_tmul_eq (modesBelow N) (positiveUEAction (MatrixSL2.color a) u) ω hω,
      ← finiteAction_tmul_eq (modesBelow N) u (PositiveCE.colorAction a ω) hL,
      ← map_add, ← constantAction_color_tmul]
    exact (finiteAction_constantAction_color_tmul N a u ω).symm
  induction z using TensorProduct.inductionOn with
  | tmul u ω => exact hpure u ω
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The action boundary is equivariant for every actual constant matrix. -/
theorem action_constantAction (x : G) (z : Chain) :
    action (constantAction x z) = constantAction x (action z) := by
  rw [← MatrixSL2.color_decomposition x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.map_smul_of_tower, action_constantAction_color]

/-- The bracket boundary is equivariant by the proved equivariance of its exterior factor. -/
theorem bracket_constantAction (x : G) (z : Chain) :
    bracket (constantAction x z) = constantAction x (bracket z) := by
  induction z using TensorProduct.inductionOn with
  | tmul u ω =>
    simp only [constantAction_tmul, map_add, bracket_tmul, boundary_positiveAction]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The actual standard free Chevalley--Eilenberg differential is constant-sl₂ equivariant. -/
theorem differential_constantAction (x : G) (z : Chain) :
    differential (constantAction x z) = constantAction x (differential z) := by
  simp only [differential, LinearMap.add_apply, action_constantAction,
    bracket_constantAction, map_add]

/-- The genuine free CE boundary as a morphism of the canonical tensor sl₂ representations. -/
def differentialLie : Chain →ₗ⁅ℂ,G⁆ Chain :=
  { differential.restrictScalars ℂ with map_lie' := fun {x z} => differential_constantAction x z }

@[simp] theorem differentialLie_apply (z : Chain) : differentialLie z = differential z := rfl

end KhanSL2.BGG.FreeCE
