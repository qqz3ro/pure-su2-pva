module

public import KhanSL2.BGG.RelativeCochainsTransfer

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The comparison preserves actual cohomological degrees. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.PositiveTransfer
open PositiveCE FiniteExterior

/-- The actual bracket part lowers exterior degree. -/
theorem bracket_mem_sourceDegree {p : ℕ} {u : Chain} (hu : u ∈ sourceDegree (p+1)) :
    FreeCE.bracket u ∈ sourceDegree p := by
  have hc := (mem_sourceDegree_iff u (p+1)).mp hu
  rw [eq_sum_tmul u, map_sum]
  apply (sourceDegree p).sum_mem
  intro s hs
  rw [FreeCE.bracket_tmul]
  apply Submodule.tmul_mem_baseChange_of_mem
  have hm : monomial s ∈ piece (p+1) (monomialEnergy s) :=
    Finsupp.single_mem_supported ℂ 1 ⟨hc s hs, rfl⟩
  exact fun t ht => (PositiveCE.boundary_mem_piece hm ht).1

theorem bracket_eq_zero_of_sourceDegree_zero {u : Chain} (hu : u ∈ sourceDegree 0) :
    FreeCE.bracket u = 0 := by
  have hc := (mem_sourceDegree_iff u 0).mp hu
  rw [eq_sum_tmul u, map_sum]
  apply Finset.sum_eq_zero
  intro s hs
  have he : s=∅ := Finset.card_eq_zero.mp (hc s hs)
  rw [he, FreeCE.bracket_tmul]
  change _ ⊗ₜ[ℂ] PositiveCE.boundary 1 = 0
  rw [PositiveCE.boundary_one, TensorProduct.tmul_zero]

theorem sourceDifferential_mem_degree {p : ℕ} {u : Chain} (hu : u ∈ sourceDegree (p+1)) :
    FreeCE.differential u ∈ sourceDegree p :=
  (sourceDegree p).add_mem (action_mem_degree hu) (bracket_mem_sourceDegree hu)

theorem sourceDifferential_eq_zero_of_degree_zero {u : Chain} (hu : u ∈ sourceDegree 0) :
    FreeCE.differential u = 0 := by
  change FreeCE.action u + FreeCE.bracket u = 0
  rw [action_eq_zero_of_degree_zero hu, bracket_eq_zero_of_sourceDegree_zero hu, add_zero]

end KhanSL2.BGG.PositiveTransfer

namespace KhanSL2.BGG.RelativeCochains
open scoped RelativeCochains
variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]

/-- A full relative cochain of degree p vanishes on all other exterior degrees. -/
def freeDegree (p : ℕ) : Submodule ℂ (FreeHom M) where
  carrier := {f | ∀ q, q ≠ p → ∀ u ∈ PositiveTransfer.sourceDegree q, f.val u = 0}
  zero_mem' := by intro q hq u hu; rfl
  add_mem' := by
    intro f g hf hg q hq u hu
    change f.val u + g.val u = 0
    rw [hf q hq u hu, hg q hq u hu, add_zero]
  smul_mem' := by
    intro r f hf q hq u hu
    change r • f.val u = 0
    rw [hf q hq u hu, smul_zero]

/-- The corresponding cohomological degree in the harmonic Hom complex. -/
def harmonicDegree (p : ℕ) : Submodule ℂ (HarmonicHom M) where
  carrier := {f | ∀ q, q ≠ p → ∀ u ∈ harmonicTensorDegree q, f.val u = 0}
  zero_mem' := by intro q hq u hu; rfl
  add_mem' := by
    intro f g hf hg q hq u hu
    change f.val u + g.val u = 0
    rw [hf q hq u hu, hg q hq u hu, add_zero]
  smul_mem' := by
    intro r f hf q hq u hu
    change r • f.val u = 0
    rw [hf q hq u hu, smul_zero]

/-- The specified CE cochain differential raises degree by one. -/
theorem differential_mem_freeDegree {p : ℕ} {f : FreeHom M} (hf : f ∈ freeDegree M p) :
    differential M f ∈ freeDegree M (p+1) := by
  intro q hq u hu
  rw [differential_apply]
  cases q with
  | zero => rw [PositiveTransfer.sourceDifferential_eq_zero_of_degree_zero hu, map_zero]
  | succ q =>
    exact hf q (fun h => hq (congrArg (·+1) h)) _
      (PositiveTransfer.sourceDifferential_mem_degree hu)

theorem harmonicDifferential_mem_harmonicDegree {p : ℕ} {f : HarmonicHom M}
    (hf : f ∈ harmonicDegree M p) : harmonicDifferential M f ∈ harmonicDegree M (p+1) := by
  intro q hq u hu
  rw [harmonicDifferential_apply]
  cases q with
  | zero => rw [PositiveTransfer.differential_eq_zero_of_degree_zero hu, map_zero]
  | succ q =>
    exact hf q (fun h => hq (congrArg (·+1) h)) _
      (PositiveTransfer.differential_mem_degree hu)

theorem toHarmonic_mem_degree {p : ℕ} {f : FreeHom M} (hf : f ∈ freeDegree M p) :
    toHarmonic M f ∈ harmonicDegree M p := by
  intro q hq u hu
  exact hf q hq _ (PositiveTransfer.contraction_incl_mem_degree hu)

theorem fromHarmonic_mem_degree {p : ℕ} {f : HarmonicHom M} (hf : f ∈ harmonicDegree M p) :
    fromHarmonic M f ∈ freeDegree M p := by
  intro q hq u hu
  exact hf q hq _ (PositiveTransfer.contraction_proj_mem_degree hu)

/-- The concrete comparison homotopy lowers positive cohomological degree by one. -/
theorem comparisonHomotopy_mem_degree {p : ℕ} {f : FreeHom M} (hf : f ∈ freeDegree M (p+1)) :
    comparisonHomotopy M f ∈ freeDegree M p := by
  intro q hq u hu
  exact hf (q+1) (fun h => hq (Nat.add_right_cancel h)) _
    (PositiveTransfer.contraction_homotopy_mem_degree hu)

/-- The comparison homotopy vanishes in cohomological degree zero. -/
theorem comparisonHomotopy_eq_zero_of_degree_zero {f : FreeHom M} (hf : f ∈ freeDegree M 0) :
    comparisonHomotopy M f = 0 := by
  apply tensorHom_ext M
  intro u
  rw [comparisonHomotopy_apply, PositiveTransfer.eq_sum_tmul u, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro s hs
  apply hf (s.card+1) (Nat.succ_ne_zero _)
  apply PositiveTransfer.contraction_homotopy_mem_degree
  exact Submodule.tmul_mem_baseChange_of_mem _ (Finsupp.single_mem_supported ℂ 1 rfl)

end KhanSL2.BGG.RelativeCochains
