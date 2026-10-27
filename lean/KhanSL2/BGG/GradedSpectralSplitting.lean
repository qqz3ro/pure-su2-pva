module

public import KhanSL2.BasisGrading
public import KhanSL2.BGG.CasimirSplitting

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Global kernel/range splitting from finite homogeneous pieces. -/
noncomputable section
namespace KhanSL2.BasisGrading

/-- A degree-preserving operator splits globally if each homogeneous vector
splits and no homogeneous vector has a nonzero image killed by the operator.
The proof uses finite-support homogeneous projections, with no completion. -/
theorem isCompl_ker_range_of_piece {α ι : Type*} [DecidableEq ι]
    (degree : α → ι) (F : Module.End ℂ (α →₀ ℂ))
    (hF : ∀ d u, u ∈ piece degree d → F u ∈ piece degree d)
    (hnil : ∀ d u, u ∈ piece degree d → F (F u) = 0 → F u = 0)
    (hspan : ∀ d, piece degree d ≤ LinearMap.ker F ⊔ LinearMap.range F) :
    IsCompl (LinearMap.ker F) (LinearMap.range F) := by
  have hproj (d : ι) (u : α →₀ ℂ) : projection degree d (F u) = F (projection degree d u) :=
    projection_linearMap degree F id Function.injective_id hF d u
  constructor
  · apply disjoint_iff.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro u hu
    obtain ⟨v, hv⟩ := hu.2
    have hFu : F u = 0 := hu.1
    have hz (d : ι) : projection degree d u = 0 := by
      have hnilv : F (F (projection degree d v)) = 0 := by
        rw [← hproj, ← hproj, hv, hFu, map_zero]
      have hv0 := hnil d (projection degree d v) (projection_mem degree d v) hnilv
      rwa [← hproj, hv] at hv0
    ext a
    have h := congrArg (fun v : α →₀ ℂ => v a) (hz (degree a))
    simpa using h
  · apply codisjoint_iff.mpr
    apply top_unique
    rw [← piece_iSup_eq_top degree]
    exact iSup_le hspan

end KhanSL2.BasisGrading
namespace KhanSL2.BGG.PositiveCE

/-- The actual exterior-degree/physical-energy label of a color monomial. -/
def bidegree (s : Finset Mode) : ℕ × ℕ := (s.card, monomialEnergy s)

theorem mem_bidegree_piece (q : ℕ × ℕ) (u : Cochain) :
    u ∈ BasisGrading.piece bidegree q ↔ u ∈ piece q.1 q.2 := by
  rcases q with ⟨d, N⟩
  simp only [BasisGrading.piece, piece, Finsupp.mem_supported, Set.mem_setOf_eq,
    bidegree, Prod.mk.injEq]

theorem energyCasimir_mem_piece {d N : ℕ} {u : Cochain} (hu : u ∈ piece d N) :
    energyCasimir u ∈ piece d N := by
  rw [energyCasimir_coe_piece d N (⟨u, hu⟩ : liePiece d N)]
  exact (spectralOperator d N ⟨u, hu⟩).property

/-- The actual global color energy/Casimir operator has complementary kernel
and range, obtained from proved finite-piece Casimir splitting. -/
theorem energyCasimir_isCompl_ker_range :
    IsCompl (LinearMap.ker energyCasimir) (LinearMap.range energyCasimir) := by
  apply BasisGrading.isCompl_ker_range_of_piece bidegree energyCasimir
  · intro q u hu
    exact (mem_bidegree_piece q _).mpr (energyCasimir_mem_piece ((mem_bidegree_piece q u).mp hu))
  · intro q u hu hzero
    let v : liePiece q.1 q.2 := ⟨u, (mem_bidegree_piece q u).mp hu⟩
    let f := (spectralOperator q.1 q.2).toLinearMap
    have hfzero : f (f v) = 0 := by
      apply Subtype.ext
      change (spectralOperator q.1 q.2 (spectralOperator q.1 q.2 v) : Cochain) = 0
      rw [← energyCasimir_coe_piece, ← energyCasimir_coe_piece]
      exact hzero
    have hmem : f v ∈ LinearMap.ker f ⊓ LinearMap.range f := ⟨hfzero, ⟨v, rfl⟩⟩
    rw [(spectralOperator_isCompl_ker_range q.1 q.2).inf_eq_bot] at hmem
    have hfv : f v = 0 := by simpa using hmem
    have hval := congrArg (fun w : liePiece q.1 q.2 => (w : Cochain)) hfv
    rw [energyCasimir_coe_piece q.1 q.2 v]
    exact hval
  · intro q u hu
    let v : liePiece q.1 q.2 := ⟨u, (mem_bidegree_piece q u).mp hu⟩
    let f := (spectralOperator q.1 q.2).toLinearMap
    have hv : v ∈ LinearMap.ker f ⊔ LinearMap.range f := by
      rw [(spectralOperator_isCompl_ker_range q.1 q.2).sup_eq_top]
      trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hv
    refine Submodule.mem_sup.mpr ⟨(a : Cochain), ?_, (b : Cochain), ?_, congrArg Subtype.val hab⟩
    · change energyCasimir (a : Cochain) = 0
      rw [energyCasimir_coe_piece]
      have ha0 : spectralOperator q.1 q.2 a = 0 := ha
      rw [ha0]
      rfl
    · obtain ⟨w, hw⟩ := hb
      refine ⟨(w : Cochain), ?_⟩
      rw [energyCasimir_coe_piece]
      exact congrArg Subtype.val hw

end KhanSL2.BGG.PositiveCE
