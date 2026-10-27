module

public import KhanSL2.Factorization.WeightedRootsAlgebra
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-! The weight-one root assignments form a single symmetric-group orbit.
These are exactly the components of the coprime labelled-root splitting. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.SymmetricFamily
open Factorization.WeightedRoots

/-- An assignment of exactly r of k labelled roots to the first factor. -/
abbrev Assignment (k r : ℕ) := {S : Finset (Fin k) // S.card = r}

@[simp] theorem assignment_card (k r : ℕ) :
    Fintype.card (Assignment k r) = Nat.choose k r := by
  simp [Assignment, Fintype.card_finset_len]

/-- The weighted-root assignment index becomes the actual r-element subsets for unit weights. -/
def assignmentEquiv (k r : ℕ) : Admissible (fun _ : Fin k => 1) r ≃ Assignment k r where
  toFun σ := ⟨selected σ.val, by simpa using σ.property⟩
  invFun S := ⟨fun i => decide (i ∈ S.val), by
    simpa [selected] using S.property⟩
  left_inv σ := by
    apply Subtype.ext
    funext i
    simp [selected]
  right_inv S := by
    apply Subtype.ext
    ext i
    simp [selected]

/-- Relabel an assignment using the actual permutation of its root slots. -/
def assignmentPermute {k r : ℕ} (σ : Equiv.Perm (Fin k)) (S : Assignment k r) : Assignment k r :=
  ⟨S.val.map σ.toEmbedding, by simpa using S.property⟩

/-- All root-assignment components are conjugate under the actual symmetric group. -/
theorem assignment_transitive {k r : ℕ} (S T : Assignment k r) :
    ∃ σ : Equiv.Perm (Fin k), assignmentPermute σ S = T := by
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_map_finset_eq S.val T.val (S.property.trans T.property.symm)
  exact ⟨σ,Subtype.ext hσ⟩

/-- The standard first block of r slots among r+s slots. -/
def firstBlock (r s : ℕ) : Assignment (r+s) r :=
  ⟨Finset.univ.map (Fin.castAddEmb s), by simp⟩

/-- Every component is a permutation of the standard block component. -/
theorem exists_permutation_firstBlock {r s : ℕ} (S : Assignment (r+s) r) :
    ∃ σ : Equiv.Perm (Fin (r+s)), assignmentPermute σ (firstBlock r s) = S :=
  assignment_transitive _ S

end KhanSL2.SymmetricFamily
