module

public import KhanSL2.BGG.FreeCEFiniteSquare
public import KhanSL2.BGG.FreeCEAugmentation

@[expose] public section
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.FreeCE
open PositiveCE FiniteExterior

/-- Exterior mode support is equivalently membership in the finite-generator subspace. -/
theorem supportModes_subset_iff (S : Finset Mode) (ω : Cochain) :
    supportModes ω ⊆ S ↔ ω ∈ generatorsIn (S : Set Mode) := by
  constructor
  · intro h s hs m hm
    exact h (subset_supportModes hs hm)
  · intro h m hm
    obtain ⟨s, hs, hms⟩ := Finset.mem_biUnion.mp hm
    exact h hs m hms

/-- Contracting an exterior word never introduces a new mode. -/
theorem supportModes_contract_subset (S : Finset Mode) (m : Mode) (ω : Cochain)
    (hω : supportModes ω ⊆ S) : supportModes (contract m ω) ⊆ S := by
  apply (supportModes_subset_iff S _).mpr
  exact contraction_mem_generatorsIn _ m ((supportModes_subset_iff S ω).mp hω)

/-- One boundary introduces only the brackets of two modes of its finite input support. -/
theorem supportModes_boundary_subset (S T : Finset Mode) (hST : S ⊆ T)
    (hmerge : ∀ m∈S, ∀ n∈S, ∀ a : Fin 3, mergeMode m n a ∈ T)
    (ω : Cochain) (hω : supportModes ω ⊆ S) : supportModes (boundary ω) ⊆ T := by
  apply (supportModes_subset_iff T _).mpr
  rw [← finiteBoundary_eq S ω hω, finiteBoundary_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro m hm
  apply Submodule.sum_mem
  intro n hn
  apply Submodule.sum_mem
  intro a _
  apply Submodule.smul_mem
  apply mul_mem_generatorsIn
  · exact generator_mem_generatorsIn _ _ (hmerge m hm n hn a)
  · apply contraction_mem_generatorsIn
    apply contraction_mem_generatorsIn
    exact (supportModes_subset_iff T ω).mp (hω.trans hST)

/-- A finite support enlarged by all brackets of pairs of its modes. -/
def bracketSupport (S : Finset Mode) : Finset Mode :=
  S ∪ S.biUnion (fun m => S.biUnion (fun n => Finset.univ.image (mergeMode m n)))

theorem subset_bracketSupport (S : Finset Mode) : S ⊆ bracketSupport S :=
  Finset.subset_union_left

theorem mergeMode_mem_bracketSupport (S : Finset Mode) (m : Mode) (hm : m∈S)
    (n : Mode) (hn : n∈S) (a : Fin 3) : mergeMode m n a ∈ bracketSupport S := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨m, hm, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨n, hn, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩

/-- The action can use the same finite cutoff twice. -/
theorem action_finiteAction (S : Finset Mode) (u : PositiveEnveloping) (ω : Cochain)
    (hω : supportModes ω ⊆ S) :
    action (finiteAction S (u ⊗ₜ[ℂ] ω)) =
      finiteAction S (finiteAction S (u ⊗ₜ[ℂ] ω)) := by
  rw [finiteAction_tmul]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact (finiteAction_tmul_eq S _ _ (supportModes_contract_subset S m ω hω)).symm

/-- The bracket cutoff on an action output still only needs the original exterior support. -/
theorem bracket_finiteAction (S T : Finset Mode) (u : PositiveEnveloping) (ω : Cochain)
    (hω : supportModes ω ⊆ S) :
    bracket (finiteAction T (u ⊗ₜ[ℂ] ω)) =
      finiteBracket S (finiteAction T (u ⊗ₜ[ℂ] ω)) := by
  rw [finiteAction_tmul]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [bracket_tmul, finiteBracket_tmul,
    finiteBoundary_eq S _ (supportModes_contract_subset S m ω hω)]

end KhanSL2.BGG.FreeCE