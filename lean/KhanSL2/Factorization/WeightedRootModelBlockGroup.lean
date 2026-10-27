module

public import KhanSL2.Factorization.WeightedRootModelBlocks
public import KhanSL2.SymmetricFamily.BlockStabilizer

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

/-- The two independent weighted block groups act honestly on all labels. -/
def weightedBlockHom (q₁ q₂ r₁ r₂ : ℕ) :
    BlockGroup q₁ r₁ × BlockGroup q₂ r₂ →* BlockGroup (q₁+q₂) (r₁+r₂) where
  toFun g := (SymmetricFamily.blockPermutationHom q₁ q₂ (g.1.1,g.2.1),
    SymmetricFamily.blockPermutationHom r₁ r₂ (g.1.2,g.2.2))
  map_one' := Prod.ext (map_one _) (map_one _)
  map_mul' g h := by
    apply Prod.ext
    · exact (SymmetricFamily.blockPermutationHom q₁ q₂).map_mul (g.1.1,g.2.1) (h.1.1,h.2.1)
    · exact (SymmetricFamily.blockPermutationHom r₁ r₂).map_mul (g.1.2,g.2.2) (h.1.2,h.2.2)

@[simp] theorem weightedBlockHom_first (q₁ q₂ r₁ r₂ : ℕ)
    (g : BlockGroup q₁ r₁ × BlockGroup q₂ r₂) (i : Fin q₁ ⊕ Fin r₁) :
    blockPermutation (weightedBlockHom q₁ q₂ r₁ r₂ g) (firstWeightedInclusion q₁ q₂ r₁ r₂ i) =
      firstWeightedInclusion q₁ q₂ r₁ r₂ (blockPermutation g.1 i) := by
  cases i <;> simp [blockPermutation,weightedBlockHom,firstWeightedInclusion]

@[simp] theorem weightedBlockHom_second (q₁ q₂ r₁ r₂ : ℕ)
    (g : BlockGroup q₁ r₁ × BlockGroup q₂ r₂) (i : Fin q₂ ⊕ Fin r₂) :
    blockPermutation (weightedBlockHom q₁ q₂ r₁ r₂ g) (secondWeightedInclusion q₁ q₂ r₁ r₂ i) =
      secondWeightedInclusion q₁ q₂ r₁ r₂ (blockPermutation g.2 i) := by
  cases i <;> simp [blockPermutation,weightedBlockHom,secondWeightedInclusion]

theorem weightedBlockHom_sign (q₁ q₂ r₁ r₂ : ℕ)
    (g : BlockGroup q₁ r₁ × BlockGroup q₂ r₂) :
    (weightedBlockHom q₁ q₂ r₁ r₂ g).1.sign = g.1.1.sign * g.2.1.sign :=
  SymmetricFamily.blockPermutation_sign q₁ q₂ (g.1.1,g.2.1)

def firstWeightedAssignment (q₁ q₂ r₁ r₂ : ℕ) :
    WeightedAssignment (q₁+q₂) (r₁+r₂) (q₁+2*r₁) :=
  ⟨fun i => decide (i ∈ firstWeightedSet q₁ q₂ r₁ r₂),by
    simp only [show selected (fun i => decide (i ∈ firstWeightedSet q₁ q₂ r₁ r₂)) =
      firstWeightedSet q₁ q₂ r₁ r₂ from by ext i; simp [selected]]
    rw [rootWeight_sum]
    simp [firstWeightedSet,SymmetricFamily.firstBlock]⟩

@[simp] theorem selected_firstWeightedAssignment (q₁ q₂ r₁ r₂ : ℕ) :
    selected (firstWeightedAssignment q₁ q₂ r₁ r₂).val = firstWeightedSet q₁ q₂ r₁ r₂ := by
  ext i
  simp [firstWeightedAssignment,selected]

theorem assignment_eq_of_selected_eq {q r b : ℕ} {σ τ : WeightedAssignment q r b}
    (h : selected σ.val = selected τ.val) : σ = τ := by
  apply Subtype.ext
  funext i
  have hi : σ.val i = true ↔ τ.val i = true := by
    simpa only [selected,Finset.mem_filter,Finset.mem_univ,true_and] using Finset.ext_iff.mp h i
  cases ha : σ.val i <;> cases hb : τ.val i <;> simp_all

/-- Independent first/second block permutations fix exactly the chosen weighted assignment. -/
theorem weightedBlockHom_fixes (q₁ q₂ r₁ r₂ : ℕ)
    (g : BlockGroup q₁ r₁ × BlockGroup q₂ r₂) :
    weightedBlockHom q₁ q₂ r₁ r₂ g • firstWeightedAssignment q₁ q₂ r₁ r₂ =
      firstWeightedAssignment q₁ q₂ r₁ r₂ := by
  apply assignment_eq_of_selected_eq
  change selected (assignmentRelabel _ _).val = _
  rw [← Finset.toLeft_disjSum_toRight (u := selected (assignmentRelabel _ _).val),
    selected_left_relabel,selected_right_relabel,selected_firstWeightedAssignment]
  have ho := congrArg Subtype.val (SymmetricFamily.blockPermutation_firstBlock q₁ q₂ (g.1.1,g.2.1))
  have he := congrArg Subtype.val (SymmetricFamily.blockPermutation_firstBlock r₁ r₂ (g.1.2,g.2.2))
  change (SymmetricFamily.firstBlock q₁ q₂).val.map
      (SymmetricFamily.blockPermutationHom q₁ q₂ (g.1.1,g.2.1)).toEmbedding = _ at ho
  change (SymmetricFamily.firstBlock r₁ r₂).val.map
      (SymmetricFamily.blockPermutationHom r₁ r₂ (g.1.2,g.2.2)).toEmbedding = _ at he
  simp only [firstWeightedSet,Finset.toLeft_disjSum,Finset.toRight_disjSum]
  change ((SymmetricFamily.firstBlock q₁ q₂).val.map
      (SymmetricFamily.blockPermutationHom q₁ q₂ (g.1.1,g.2.1)).toEmbedding).disjSum
      ((SymmetricFamily.firstBlock r₁ r₂).val.map
        (SymmetricFamily.blockPermutationHom r₁ r₂ (g.1.2,g.2.2)).toEmbedding) =
    (SymmetricFamily.firstBlock q₁ q₂).val.disjSum (SymmetricFamily.firstBlock r₁ r₂).val
  rw [ho,he]

/-- Every stabilizing weighted permutation has these two independent block actions. -/
theorem weightedBlockHom_covers (q₁ q₂ r₁ r₂ : ℕ)
    (g : BlockGroup (q₁+q₂) (r₁+r₂))
    (hg : g • firstWeightedAssignment q₁ q₂ r₁ r₂ = firstWeightedAssignment q₁ q₂ r₁ r₂) :
    ∃ h : BlockGroup q₁ r₁ × BlockGroup q₂ r₂, weightedBlockHom q₁ q₂ r₁ r₂ h = g := by
  have hs := congrArg (fun σ => selected σ.val) hg
  have hl := congrArg Finset.toLeft hs
  have hr := congrArg Finset.toRight hs
  change (selected (assignmentRelabel g _).val).toLeft = _ at hl
  change (selected (assignmentRelabel g _).val).toRight = _ at hr
  rw [selected_left_relabel,selected_firstWeightedAssignment] at hl
  rw [selected_right_relabel,selected_firstWeightedAssignment] at hr
  have hl' : g.1 • SymmetricFamily.firstBlock q₁ q₂ = SymmetricFamily.firstBlock q₁ q₂ := by
    apply Subtype.ext
    change (SymmetricFamily.firstBlock q₁ q₂).val.map g.1.toEmbedding = _
    simpa only [firstWeightedSet,Finset.toLeft_disjSum] using hl
  have hr' : g.2 • SymmetricFamily.firstBlock r₁ r₂ = SymmetricFamily.firstBlock r₁ r₂ := by
    apply Subtype.ext
    change (SymmetricFamily.firstBlock r₁ r₂).val.map g.2.toEmbedding = _
    simpa only [firstWeightedSet,Finset.toRight_disjSum] using hr
  obtain ⟨a,ha⟩ := (SymmetricFamily.blockStabilizerEquiv q₁ q₂).surjective ⟨g.1,hl'⟩
  obtain ⟨b,hb⟩ := (SymmetricFamily.blockStabilizerEquiv r₁ r₂).surjective ⟨g.2,hr'⟩
  exact ⟨((a.1,b.1),(a.2,b.2)),Prod.ext (congrArg Subtype.val ha) (congrArg Subtype.val hb)⟩

/-- The orbit label of the explicit first weighted blocks. -/
def firstWeightedOrbitIndex (q₁ q₂ r₁ r₂ : ℕ) :
    OrbitIndex (q₁+q₂) (r₁+r₂) (q₁+2*r₁) :=
  ⟨(q₁,r₁),Nat.le_add_right _ _,Nat.le_add_right _ _,rfl⟩

@[simp] theorem orbitRepresentative_firstWeightedOrbitIndex (q₁ q₂ r₁ r₂ : ℕ) :
    orbitRepresentative (firstWeightedOrbitIndex q₁ q₂ r₁ r₂) =
      firstWeightedAssignment q₁ q₂ r₁ r₂ := by
  apply Subtype.ext
  funext i
  rfl
end KhanSL2.Factorization.WeightedRootModel




