module

public import KhanSL2.Chains.Transpose
public import KhanSL2.CEEquivariance
public import KhanSL2.CESquareZero
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section

/-!
# The coinvariant chain complex

The chain boundary is the graded transpose of the CE differential `q`, and the
color coaction is the transpose of the color action. Coinvariant chains are
chains modulo the span of the coaction images. Its homology in a fixed degree
is the finite-dimensional space `ChainHomology d`.
-/

noncomputable section

namespace KhanSL2

/-- The CE differential raises the total degree by one. -/
theorem q_isHomogeneous : IsHomogeneousOp q (1, 0, 0) := fun _ _ hu => q_degree hu

theorem colorAction_isHomogeneous (a : Fin 3) : IsHomogeneousOp (colorAction a) 0 :=
  fun _ _ hu => by simpa using colorAction_degree a hu

/-- The chain boundary: the graded transpose of `q`. -/
def boundary : Chain →ₗ[ℂ] Chain := gradedTranspose q (1, 0, 0)

/-- The color coaction: the graded transpose of the color action. -/
def coaction (a : Fin 3) : Chain →ₗ[ℂ] Chain := gradedTranspose (colorAction a) 0

theorem pairing_q (u : Cochain) (ζ : Chain) :
    pairing (q u) ζ = pairing u (boundary ζ) :=
  pairing_gradedTranspose q _ q_isHomogeneous u ζ

theorem pairing_colorAction (a : Fin 3) (u : Cochain) (ζ : Chain) :
    pairing (colorAction a u) ζ = pairing u (coaction a ζ) :=
  pairing_gradedTranspose _ _ (colorAction_isHomogeneous a) u ζ

theorem boundary_degree {d : Degree} {ζ : Chain} (hζ : ζ ∈ cochainPiece d) :
    boundary ζ ∈ cochainPiece (d - (1, 0, 0)) :=
  gradedTranspose_degree q _ q_isHomogeneous hζ

theorem coaction_degree (a : Fin 3) {d : Degree} {ζ : Chain} (hζ : ζ ∈ cochainPiece d) :
    coaction a ζ ∈ cochainPiece d := by
  simpa [coaction] using gradedTranspose_degree _ _ (colorAction_isHomogeneous a) hζ

theorem boundary_boundary (ζ : Chain) : boundary (boundary ζ) = 0 := by
  apply chain_ext
  intro u
  rw [← pairing_q, ← pairing_q, q_square_zero]
  simp

theorem coaction_boundary (a : Fin 3) (ζ : Chain) :
    coaction a (boundary ζ) = boundary (coaction a ζ) := by
  apply chain_ext
  intro u
  rw [← pairing_colorAction, ← pairing_q, ← pairing_q, ← pairing_colorAction,
    q_colorAction]

/-- The span of all coaction images: chains that vanish in coinvariants. -/
def relations : Submodule ℂ Chain := ⨆ a : Fin 3, LinearMap.range (coaction a)

theorem boundary_mem_relations {ζ : Chain} (hζ : ζ ∈ relations) :
    boundary ζ ∈ relations := by
  refine Submodule.iSup_induction _ (motive := fun ζ => boundary ζ ∈ relations) hζ ?_ ?_ ?_
  · rintro a _ ⟨ξ, rfl⟩
    rw [← coaction_boundary]
    exact Submodule.mem_iSup_of_mem a ⟨_, rfl⟩
  · simp
  · intro ζ ξ hζ hξ
    rw [map_add]; exact Submodule.add_mem _ hζ hξ

/-- An invariant cochain pairs to zero with every relation. -/
theorem pairing_relations_eq_zero {u : Cochain} (hu : u ∈ relativeInvariants)
    {ζ : Chain} (hζ : ζ ∈ relations) : pairing u ζ = 0 := by
  rw [mem_relativeInvariants_iff] at hu
  refine Submodule.iSup_induction _ (motive := fun ζ => pairing u ζ = 0) hζ ?_ ?_ ?_
  · rintro a _ ⟨ξ, rfl⟩
    rw [← pairing_colorAction, hu a]
    simp
  · simp
  · intro ζ ξ hζ hξ
    rw [map_add, hζ, hξ, add_zero]

/-- A homogeneous cochain orthogonal to the relations of its degree is invariant. -/
theorem mem_relativeInvariants_of_pairing {d : Degree} {u : Cochain}
    (hu : u ∈ cochainPiece d)
    (h : ∀ ζ ∈ relations, ζ ∈ cochainPiece d → pairing u ζ = 0) :
    u ∈ relativeInvariants := by
  rw [mem_relativeInvariants_iff]
  intro a
  apply cochain_eq_zero_of_pairing (colorAction_degree a hu)
  intro s hs
  rw [pairing_colorAction]
  apply h
  · exact Submodule.mem_iSup_of_mem a ⟨_, rfl⟩
  · exact hs ▸ coaction_degree a (cochain_single_mem s 1)

/-! ## Homology in a fixed degree -/

/-- Chains of degree `d` whose boundary vanishes in coinvariants. -/
def cycles (d : Degree) : Submodule ℂ Chain :=
  cochainPiece d ⊓ relations.comap boundary

/-- Relations of degree `d` together with boundaries of chains of degree `d + (1,0,0)`. -/
def bounds (d : Degree) : Submodule ℂ Chain :=
  (relations ⊓ cochainPiece d) ⊔ (cochainPiece (d + (1, 0, 0))).map boundary

theorem bounds_le_cycles (d : Degree) : bounds d ≤ cycles d := by
  apply sup_le
  · rintro ζ ⟨hrel, hd⟩
    exact ⟨hd, boundary_mem_relations hrel⟩
  · rintro _ ⟨ξ, hξ, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa using boundary_degree hξ
    · change boundary (boundary ξ) ∈ relations
      rw [boundary_boundary]; exact Submodule.zero_mem _

/-- The homology of coinvariant chains in degree `d`. -/
abbrev ChainHomology (d : Degree) : Type :=
  ↥(cycles d) ⧸ (bounds d).comap (cycles d).subtype

theorem degreeMonomials_finite_piece (d : Degree) :
    cochainPiece d ≤ Submodule.span ℂ
      ((fun s => (Finsupp.single s 1 : Chain)) '' (degreeMonomials d : Set ExteriorMonomial)) := by
  intro ζ hζ
  rw [chain_eq_sum_of_mem hζ]
  apply Submodule.sum_mem
  intro s hs
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨s, hs, rfl⟩

instance (d : Degree) : FiniteDimensional ℂ (cochainPiece d) := by
  have hspan : FiniteDimensional ℂ (Submodule.span ℂ
      ((fun s => (Finsupp.single s 1 : Chain)) '' (degreeMonomials d : Set ExteriorMonomial))) :=
    FiniteDimensional.span_of_finite ℂ ((degreeMonomials d).finite_toSet.image _)
  exact Submodule.finiteDimensional_of_le (degreeMonomials_finite_piece d)

instance (d : Degree) : FiniteDimensional ℂ (cycles d) :=
  Submodule.finiteDimensional_of_le (inf_le_left : cycles d ≤ cochainPiece d)

instance (d : Degree) : FiniteDimensional ℂ (ChainHomology d) := inferInstance

end KhanSL2
