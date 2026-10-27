module

public import KhanSL2.Factorization.WeightedRootModelAssignments
public import KhanSL2.Factorization.OrbitStabilizerOrbits

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace KhanSL2.Factorization.WeightedRootModel
open WeightedRoots

theorem rootWeight_sum (q r : ℕ) (S : Finset (Fin q ⊕ Fin r)) :
    (∑ i ∈ S, rootWeight q r i) = S.toLeft.card + 2*S.toRight.card := by
  rw [← Finset.toLeft_disjSum_toRight (u := S),Finset.sum_disjSum]
  simp [rootWeight,Nat.mul_comm]

theorem assignmentCounts_spec {q r b : ℕ} (σ : WeightedAssignment q r b) :
    (assignmentCounts σ).1 ≤ q ∧ (assignmentCounts σ).2 ≤ r ∧
      (assignmentCounts σ).1 + 2*(assignmentCounts σ).2 = b := by
  refine ⟨?_,?_,?_⟩
  · exact (Finset.card_le_univ (s := (selected σ.val).toLeft)).trans_eq (Fintype.card_fin q)
  · exact (Finset.card_le_univ (s := (selected σ.val).toRight)).trans_eq (Fintype.card_fin r)
  · exact (rootWeight_sum q r (selected σ.val)).symm.trans σ.property

/-- The precise admissible odd/even allocations to the first polynomial factor. -/
def OrbitIndex (q r b : ℕ) := {d : ℕ × ℕ // d.1 ≤ q ∧ d.2 ≤ r ∧ d.1 + 2*d.2 = b}

instance (q r b : ℕ) : Finite (OrbitIndex q r b) := by
  let f : OrbitIndex q r b → Fin (q+1) × Fin (r+1) :=
    fun d => (⟨d.val.1,by have := d.property.1; omega⟩,⟨d.val.2,by have := d.property.2.1; omega⟩)
  apply Finite.of_injective f
  intro a c h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun x : Fin (q+1) × Fin (r+1) => x.1.val) h
  · exact congrArg (fun x : Fin (q+1) × Fin (r+1) => x.2.val) h
instance (q r b : ℕ) : Fintype (OrbitIndex q r b) := Fintype.ofFinite _

def orbitOfAssignment {q r b : ℕ} (σ : WeightedAssignment q r b) : OrbitIndex q r b :=
  ⟨assignmentCounts σ,assignmentCounts_spec σ⟩

def representativeSet {q r b : ℕ} (d : OrbitIndex q r b) : Finset (Fin q ⊕ Fin r) :=
  (Finset.univ.map (Fin.castLEEmb d.property.1)).disjSum
    (Finset.univ.map (Fin.castLEEmb d.property.2.1))

theorem representativeSet_weight {q r b : ℕ} (d : OrbitIndex q r b) :
    (∑ i ∈ representativeSet d, rootWeight q r i) = b := by
  rw [rootWeight_sum]
  simpa only [representativeSet,Finset.toLeft_disjSum,Finset.toRight_disjSum,
    Finset.card_map,Finset.card_univ,Fintype.card_fin] using d.property.2.2

/-- Canonical first-block representative, rather than an unnormalized choice of orbit vector. -/
def orbitRepresentative {q r b : ℕ} (d : OrbitIndex q r b) : WeightedAssignment q r b :=
  ⟨fun i => decide (i ∈ representativeSet d),by
    simpa [selected] using representativeSet_weight d⟩

@[simp] theorem selected_orbitRepresentative {q r b : ℕ} (d : OrbitIndex q r b) :
    selected (orbitRepresentative d).val = representativeSet d := by
  ext i
  simp [orbitRepresentative,selected]

@[simp] theorem assignmentCounts_orbitRepresentative {q r b : ℕ} (d : OrbitIndex q r b) :
    assignmentCounts (orbitRepresentative d) = d.val := by
  simp only [assignmentCounts,selected_orbitRepresentative,representativeSet,
    Finset.toLeft_disjSum,Finset.toRight_disjSum,Finset.card_map,Finset.card_univ,Fintype.card_fin]

theorem orbitRepresentative_separate {q r b : ℕ} (a d : OrbitIndex q r b) (g : BlockGroup q r)
    (h : g • orbitRepresentative a = orbitRepresentative d) : a = d := by
  apply Subtype.ext
  have hc := congrArg assignmentCounts h
  change assignmentCounts (assignmentRelabel g (orbitRepresentative a)) =
    assignmentCounts (orbitRepresentative d) at hc
  simpa only [assignmentCounts_relabel,assignmentCounts_orbitRepresentative] using hc

theorem orbitRepresentative_cover {q r b : ℕ} (σ : WeightedAssignment q r b) :
    ∃ (d : OrbitIndex q r b) (g : BlockGroup q r), g • orbitRepresentative d = σ := by
  refine ⟨orbitOfAssignment σ,?_⟩
  exact assignment_transitive_same_counts (orbitRepresentative (orbitOfAssignment σ)) σ
    (assignmentCounts_orbitRepresentative _)

/-- Weighted assignments have precisely the stated finite orbit decomposition. -/
def weightedOrbitEvaluationEquiv {q r b : ℕ} {R : Type*} [CommRing R]
    {M : WeightedAssignment q r b → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (T : FiberTransport (R:=R) (G:=BlockGroup q r) M) :
    T.invariantSections ≃ₗ[R] ∀ d : OrbitIndex q r b, T.stabilizerFixed (orbitRepresentative d) :=
  T.orbitEvaluationEquiv orbitRepresentative orbitRepresentative_separate orbitRepresentative_cover

end KhanSL2.Factorization.WeightedRootModel

