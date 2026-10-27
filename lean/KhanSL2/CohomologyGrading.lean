module

public import KhanSL2.GradingDecomposition
public import KhanSL2.CEDegrees

@[expose] public section

/-! The genuine internal grading of invariant cycles and their cohomology quotient. -/

noncomputable section

namespace KhanSL2

theorem cochainProjection_colorAction (d : Degree) (a : Fin 3) (u : Cochain) :
    cochainProjection d (colorAction a u) = colorAction a (cochainProjection d u) := by
  simpa using cochainProjection_linearMap (colorAction a) 0
    (fun _ _ hu => by simpa using colorAction_degree a hu) d u

theorem cochainProjection_q (d : Degree) (u : Cochain) :
    cochainProjection (d + (1, 0, 0)) (q u) = q (cochainProjection d u) :=
  cochainProjection_linearMap q (1, 0, 0) (fun _ _ hu => q_degree hu) d u

theorem cochainProjection_invariant (d : Degree) {u : Cochain}
    (hu : u ∈ relativeInvariants) : cochainProjection d u ∈ relativeInvariants := by
  rw [relativeInvariants, Submodule.mem_iInf] at hu ⊢
  intro a
  change colorAction a (cochainProjection d u) = 0
  rw [← cochainProjection_colorAction, LinearMap.mem_ker.mp (hu a), map_zero]

theorem cochainProjection_cycle (d : Degree) {u : Cochain}
    (hu : u ∈ relativeCycles) : cochainProjection d u ∈ relativeCycles := by
  refine ⟨cochainProjection_invariant d hu.1, ?_⟩
  change q (cochainProjection d u) = 0
  rw [← cochainProjection_q, LinearMap.mem_ker.mp hu.2, map_zero]

def cochainDecomposition : GradingDecomposition cochainPiece :=
  BasisGrading.decomposition monomialDegree

@[simp] theorem cochainDecomposition_apply (u : Cochain) (d : Degree) :
    cochainDecomposition.components u d = cochainProjection d u :=
  BasisGrading.coaction_apply monomialDegree u d

def cycleDecomposition : GradingDecomposition
    (fun d => (cochainPiece d).comap relativeCycles.subtype) :=
  cochainDecomposition.restrict relativeCycles
    (fun u hu d => by
      rw [cochainDecomposition_apply]
      exact cochainProjection_cycle d hu)

@[simp] theorem cycleDecomposition_apply (u : CycleSpace) (d : Degree) :
    (cycleDecomposition.components u d : Cochain) = cochainProjection d u := by
  change cochainDecomposition.components u d = _
  exact cochainDecomposition_apply u d

theorem cycleDecomposition_boundary (v : CycleSpace) (hv : v ∈ relativeBoundaries)
    (d : Degree) : cycleDecomposition.components v d ∈ relativeBoundaries := by
  change (v : Cochain) ∈ relativeInvariants.map q at hv
  obtain ⟨u, hu, hq⟩ := hv
  change (cycleDecomposition.components v d : Cochain) ∈ relativeInvariants.map q
  refine ⟨cochainProjection (d - (1, 0, 0)) u,
    cochainProjection_invariant _ hu, ?_⟩
  rw [← cochainProjection_q, sub_add_cancel, hq, cycleDecomposition_apply]

def cohomologyDecomposition : GradingDecomposition cohomologyPiece :=
  cycleDecomposition.quotient relativeBoundaries cycleDecomposition_boundary

theorem cycle_grading_internal :
    DirectSum.IsInternal (fun d => (cochainPiece d).comap relativeCycles.subtype) :=
  cycleDecomposition.isInternal

theorem cohomology_grading_internal : DirectSum.IsInternal cohomologyPiece :=
  cohomologyDecomposition.isInternal

theorem cohomologyHomogeneous_iff_mem (d : Degree) (h : Cohomology) :
    cohomologyHomogeneous d h ↔ h ∈ cohomologyPiece d := by
  constructor
  · rintro ⟨u, hu, hd, hh⟩
    exact ⟨⟨u, hu⟩, hd, hh⟩
  · rintro ⟨u, hu, hh⟩
    exact ⟨u, u.property, hu, hh⟩

end KhanSL2
