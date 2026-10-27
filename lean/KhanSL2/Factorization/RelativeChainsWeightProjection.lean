module

public import KhanSL2.Macdonald.StrongBridgeGrading
public import KhanSL2.Macdonald.StrongBridgeInvariants
public import KhanSL2.BasisGrading

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Finite loop-weight/symmetric-degree projections on the actual chain model.
They commute with both the genuine boundary and the constant Lie action. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Factorization
open Macdonald

abbrev weightBlockDegree (b : BasisIndex) : ℕ × ℕ := (weight b, symmetricDegree b)

theorem mem_weightBlock_coordinates (w s : ℕ) (u : W) :
    basis.repr u ∈ BasisGrading.piece weightBlockDegree (w,s) ↔
      u ∈ weightDegreePiece w s := by
  change (∀ b ∈ (basis.repr u).support, (weight b, symmetricDegree b) = (w,s)) ↔ _
  simp only [Prod.mk.injEq, mem_weightDegreePiece_iff]

/-- The finite-support coordinate projection, transported by the actual mixed basis. -/
def weightProjection (w s : ℕ) : Module.End ℂ W :=
  basis.repr.symm.toLinearMap.comp
    ((BasisGrading.projection weightBlockDegree (w,s)).comp basis.repr.toLinearMap)

@[simp] theorem weightProjection_repr (w s : ℕ) (u : W) :
    basis.repr (weightProjection w s u) =
      BasisGrading.projection weightBlockDegree (w,s) (basis.repr u) := by
  simp [weightProjection]

theorem weightProjection_mem (w s : ℕ) (u : W) :
    weightProjection w s u ∈ weightDegreePiece w s := by
  rw [← mem_weightBlock_coordinates, weightProjection_repr]
  exact BasisGrading.projection_mem _ _ _

theorem weightProjection_of_mem {w s : ℕ} {u : W}
    (hu : u ∈ weightDegreePiece w s) : weightProjection w s u = u := by
  apply basis.repr.injective
  rw [weightProjection_repr]
  exact BasisGrading.projection_of_mem _ ((mem_weightBlock_coordinates w s u).mpr hu)

theorem weightProjection_of_mem_ne {w s w' s' : ℕ}
    (hne : (w,s) ≠ (w',s')) {u : W} (hu : u ∈ weightDegreePiece w' s') :
    weightProjection w s u = 0 := by
  apply basis.repr.injective
  rw [weightProjection_repr, map_zero]
  exact BasisGrading.projection_of_mem_ne _ hne
    ((mem_weightBlock_coordinates w' s' u).mpr hu)

@[simp] theorem weightProjection_basis (w s : ℕ) (b : BasisIndex) :
    weightProjection w s (basis b) =
      if weightBlockDegree b = (w,s) then basis b else 0 := by
  apply basis.repr.injective
  rw [weightProjection_repr, Module.Basis.repr_self, BasisGrading.projection_single]
  split <;> simp

/-- Every endomorphism preserving the actual finite blocks commutes with their projections. -/
theorem weightProjection_commute (F : Module.End ℂ W) (hF : PreservesWeightDegree F)
    (w s : ℕ) (u : W) : weightProjection w s (F u) = F (weightProjection w s u) := by
  have h : (weightProjection w s).comp F = F.comp (weightProjection w s) := by
    apply basis.ext
    intro b
    change weightProjection w s (F (basis b)) = F (weightProjection w s (basis b))
    rw [weightProjection_basis]
    by_cases hb : weightBlockDegree b = (w,s)
    · rw [if_pos hb]
      have hmem := hF (weight b) (symmetricDegree b) (basis b) (basis_mem_weightDegreePiece b)
      obtain ⟨hw,hs⟩ := Prod.mk.inj hb
      rw [hw,hs] at hmem
      exact weightProjection_of_mem hmem
    · rw [if_neg hb, map_zero]
      exact weightProjection_of_mem_ne (Ne.symm hb)
        (hF _ _ _ (basis_mem_weightDegreePiece b))
  exact LinearMap.congr_fun h u

theorem tensorColorAction_preservesWeightDegree (a : Fin 3) :
    PreservesWeightDegree (tensorColorAction a) := by
  intro w s u hu
  obtain ⟨v,rfl⟩ := strongModel.surjective u
  rw [← strongModel_Y, strongModel_mem_weightDegreePiece]
  exact StrongMacdonald.mapsTo_piece (StrongMacdonald.Wt_comm_Y a)
    (StrongMacdonald.Sd_comm_Y a) ((strongModel_mem_weightDegreePiece v w s).mp hu)

theorem weightProjection_colorAction (w s : ℕ) (a : Fin 3) (u : W) :
    weightProjection w s (tensorColorAction a u) =
      tensorColorAction a (weightProjection w s u) :=
  weightProjection_commute _ (tensorColorAction_preservesWeightDegree a) w s u

theorem weightProjection_chainBoundary (w s : ℕ) (u : W) :
    weightProjection w s (chainBoundary u) = chainBoundary (weightProjection w s u) :=
  weightProjection_commute _ chainBoundary_preservesWeightDegree w s u

theorem weightProjection_differential (w s : ℕ) (u : W) :
    weightProjection w s (Macdonald.differential u) =
      Macdonald.differential (weightProjection w s u) :=
  weightProjection_commute Macdonald.differential (by
    intro w' s' v hv
    exact Macdonald.restrictedTranspose_mem_weightDegree chainBoundary hv) w s u

/-- A block-supported functional only sees the matching block of its argument. -/
theorem pairing_weightProjection {w s : ℕ} {u : W}
    (hu : u ∈ weightDegreePiece w s) (v : W) :
    Macdonald.pairing u (weightProjection w s v) = Macdonald.pairing u v := by
  rw [eq_sum_basis v]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [weightProjection_basis]
  by_cases hd : weightBlockDegree b = (w,s)
  · rw [if_pos hd]
  · rw [if_neg hd, map_zero, smul_zero]
    rw [pairing_blocks_eq_zero hu (basis_mem_weightDegreePiece b) (Ne.symm hd), smul_zero]

end KhanSL2.Factorization
