module

public import KhanSL2.TargetPVA

@[expose] public section

/-! Representative formulas and degrees for the canonical map's target. -/

noncomputable section
open scoped BigOperators

namespace KhanSL2

@[simp] theorem classOf_zero (h : (0 : Cochain) ∈ relativeCycles) :
    classOf 0 h = 0 := rfl

theorem classOf_add (u v : Cochain) (hu : u ∈ relativeCycles)
    (hv : v ∈ relativeCycles) :
    classOf (u + v) (relativeCycles.add_mem hu hv) = classOf u hu + classOf v hv := rfl

theorem classOf_smul (r : ℂ) (u : Cochain) (hu : u ∈ relativeCycles) :
    classOf (r • u) (relativeCycles.smul_mem r hu) = r • classOf u hu := rfl

theorem classOf_eq_zero_iff (u : Cochain) (hu : u ∈ relativeCycles) :
    classOf u hu = 0 ↔ ∃ v ∈ relativeInvariants, q v = u := by
  change (Submodule.Quotient.mk (⟨u, hu⟩ : CycleSpace) : Cohomology) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero relativeBoundaries]
  rfl

theorem target_one_classOf : targetData.one = classOf cochainOne one_mem_cycles := rfl

theorem target_mul_classOf (u v : Cochain) (hu : u ∈ relativeCycles)
    (hv : v ∈ relativeCycles) :
    targetData.mul (classOf u hu) (classOf v hv) =
      classOf (wedge u v) (cycle_wedge hu hv) := rfl

theorem target_translation_classOf (u : Cochain) (hu : u ∈ relativeCycles) :
    targetData.translation (classOf u hu) =
      classOf (translation u)
        (CohomologyDescent.cycle_translation relativeComplex_laws.translation_commutes hu) := rfl

theorem target_bracket_classOf (u v : Cochain) (hu : u ∈ relativeCycles)
    (hv : v ∈ relativeCycles) (n : ℕ) :
    targetBracket (classOf u hu) (classOf v hv) n =
      classOf (BC.bracket u v n)
        (CohomologyDescent.cycle_bracket relativeBracket_compatibility hu hv n) := rfl

theorem classOf_mem_piece {u : Cochain} {d : Degree} (hu : u ∈ relativeCycles)
    (hd : u ∈ cochainPiece d) : classOf u hu ∈ targetData.piece d :=
  ⟨⟨u, hu⟩, hd, rfl⟩

theorem xRepresentative_degree : xRepresentative ∈ cochainPiece (2, 1, 2) := by
  apply (cochainPiece _).neg_mem
  apply (cochainPiece _).sum_mem
  intro a _
  exact cochain_wedge_mem (cochain_generator_mem (.b 0 a))
    (cochain_generator_mem (.c 0 a))

theorem yRepresentative_degree : yRepresentative ∈ cochainPiece (3, 3, 3) :=
  cochain_wedge_mem (cochain_wedge_mem (cochain_generator_mem (.b 0 0))
    (cochain_generator_mem (.b 0 1))) (cochain_generator_mem (.b 0 2))

theorem xClass_degree : xClass ∈ targetData.piece (2, 1, 2) :=
  classOf_mem_piece xRepresentative_mem_cycles xRepresentative_degree

theorem yClass_degree : yClass ∈ targetData.piece (3, 3, 3) :=
  classOf_mem_piece yRepresentative_mem_cycles yRepresentative_degree

end KhanSL2
