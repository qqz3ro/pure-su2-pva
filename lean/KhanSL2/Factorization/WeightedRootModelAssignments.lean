module

public import KhanSL2.Factorization.WeightedRootModelAction
public import KhanSL2.Factorization.WeightedRootModelBaseChange
public import KhanSL2.SymmetricFamily.Assignments
public import Mathlib.Data.Finset.Sum

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

abbrev WeightedAssignment (q r b : ℕ) := Admissible (rootWeight q r) b

theorem rootWeight_blockPermutation {q r : ℕ} (g : BlockGroup q r) (i : Fin q ⊕ Fin r) :
    rootWeight q r (blockPermutation g i) = rootWeight q r i := by
  cases i <;> rfl

theorem selected_precomp_symm {I : Type*} [Fintype I] [DecidableEq I]
    (e : Equiv.Perm I) (σ : I → Bool) :
    selected (σ ∘ e.symm) = (selected σ).map e.toEmbedding := by
  ext i
  simp [selected]

/-- Actual relabelling preserves admissibility because it preserves both root multiplicities. -/
def assignmentRelabel {q r b : ℕ} (g : BlockGroup q r) (σ : WeightedAssignment q r b) :
    WeightedAssignment q r b :=
  ⟨σ.val ∘ (blockPermutation g).symm,by
    rw [selected_precomp_symm,Finset.sum_map]
    simpa only [Equiv.coe_toEmbedding,rootWeight_blockPermutation] using σ.property⟩

@[simp] theorem selected_assignmentRelabel {q r b : ℕ} (g : BlockGroup q r)
    (σ : WeightedAssignment q r b) :
    selected (assignmentRelabel g σ).val = (selected σ.val).map (blockPermutation g).toEmbedding :=
  selected_precomp_symm _ _

instance assignmentAction (q r b : ℕ) : MulAction (BlockGroup q r) (WeightedAssignment q r b) where
  smul := assignmentRelabel
  one_smul σ := by
    apply Subtype.ext
    funext i
    cases i <;> rfl
  mul_smul g h σ := by
    apply Subtype.ext
    funext i
    cases i <;> rfl

/-- The pair of root counts indexes the weighted-assignment orbits. -/
def assignmentCounts {q r b : ℕ} (σ : WeightedAssignment q r b) : ℕ × ℕ :=
  ((selected σ.val).toLeft.card,(selected σ.val).toRight.card)

theorem selected_left_relabel {q r b : ℕ} (g : BlockGroup q r) (σ : WeightedAssignment q r b) :
    (selected (assignmentRelabel g σ).val).toLeft =
      (selected σ.val).toLeft.map g.1.toEmbedding := by
  ext i
  simp [selected_assignmentRelabel,Finset.mem_map_equiv,blockPermutation]

theorem selected_right_relabel {q r b : ℕ} (g : BlockGroup q r) (σ : WeightedAssignment q r b) :
    (selected (assignmentRelabel g σ).val).toRight =
      (selected σ.val).toRight.map g.2.toEmbedding := by
  ext i
  simp [selected_assignmentRelabel,Finset.mem_map_equiv,blockPermutation]

@[simp] theorem assignmentCounts_relabel {q r b : ℕ} (g : BlockGroup q r)
    (σ : WeightedAssignment q r b) : assignmentCounts (assignmentRelabel g σ) = assignmentCounts σ := by
  simp only [assignmentCounts,selected_left_relabel,selected_right_relabel,Finset.card_map]

/-- Equal odd/even counts are sufficient for two actual assignments to be conjugate. -/
theorem assignment_transitive_same_counts {q r b : ℕ} (σ τ : WeightedAssignment q r b)
    (hc : assignmentCounts σ = assignmentCounts τ) :
    ∃ g : BlockGroup q r, assignmentRelabel g σ = τ := by
  have hl : (selected σ.val).toLeft.card = (selected τ.val).toLeft.card := congrArg Prod.fst hc
  have hr : (selected σ.val).toRight.card = (selected τ.val).toRight.card := congrArg Prod.snd hc
  obtain ⟨g,hg⟩ := Equiv.Perm.exists_map_finset_eq (selected σ.val).toLeft (selected τ.val).toLeft hl
  obtain ⟨h,hh⟩ := Equiv.Perm.exists_map_finset_eq (selected σ.val).toRight (selected τ.val).toRight hr
  refine ⟨(g,h),?_⟩
  have hs : selected (assignmentRelabel (g,h) σ).val = selected τ.val := by
    rw [← Finset.toLeft_disjSum_toRight (u := selected (assignmentRelabel (g,h) σ).val),
      selected_left_relabel,selected_right_relabel,hg,hh,Finset.toLeft_disjSum_toRight]
  apply Subtype.ext
  funext i
  have hi : (assignmentRelabel (g,h) σ).val i = true ↔ τ.val i = true := by
    simpa only [selected,Finset.mem_filter,Finset.mem_univ,true_and] using (Finset.ext_iff.mp hs i)
  cases ha : (assignmentRelabel (g,h) σ).val i <;> cases hb : τ.val i <;>
    simp_all [selected]

end KhanSL2.Factorization.WeightedRootModel

