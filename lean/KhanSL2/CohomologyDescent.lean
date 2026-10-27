module

public import KhanSL2.PVASubquotient
public import KhanSL2.CEInvariantBasics
public import KhanSL2.CohomologyGrading
public import KhanSL2.Data

@[expose] public section

/-! Descent to the previously defined relative CE cohomology.
The input identities are explicit properties of the fixed differential;
the concrete target construction discharges them in its own theorem. -/

noncomputable section

namespace KhanSL2

structure RelativeBracketCompatibility (br : LambdaBracket Cochain) : Prop where
  invariant : ∀ u v n, u ∈ relativeInvariants → v ∈ relativeInvariants →
    br u v n ∈ relativeInvariants
  differential : ∀ u v n, u ∈ relativeInvariants → v ∈ relativeInvariants →
    q (br u v n) = br (q u) v n + br (cochainParity u) (q v) n

namespace CohomologyDescent

variable {br : LambdaBracket Cochain}
  (hT : ∀ u ∈ relativeInvariants, q (translation u) = translation (q u))
  (hbr : RelativeBracketCompatibility br)

include hT in
theorem cycle_translation {u : Cochain} (hu : u ∈ relativeCycles) :
    translation u ∈ relativeCycles := by
  refine ⟨invariant_translation hu.1, ?_⟩
  change q (translation u) = 0
  rw [hT u hu.1, LinearMap.mem_ker.mp hu.2, map_zero]

include hbr in
theorem cycle_bracket {u v : Cochain}
    (hu : u ∈ relativeCycles) (hv : v ∈ relativeCycles) (n : ℕ) :
    br u v n ∈ relativeCycles := by
  refine ⟨hbr.invariant u v n hu.1 hv.1, ?_⟩
  change q (br u v n) = 0
  rw [hbr.differential u v n hu.1 hv.1,
    LinearMap.mem_ker.mp hu.2, LinearMap.mem_ker.mp hv.2]
  simp

include hT hbr in
theorem cycles : PVAClosedSubmodule cochainData br relativeCycles where
  one_mem := one_mem_cycles
  mul_mem _ _ hu hv := cycle_wedge hu hv
  translation_mem _ hu := cycle_translation hT hu
  bracket_mem _ _ n hu hv := cycle_bracket hbr hu hv n

theorem boundaries : PVAIdeal (cycles hT hbr).data (cycles hT hbr).bracket
    relativeBoundaries where
  mul_left a b ha := by
    change (a : Cochain) ∈ relativeInvariants.map q at ha
    obtain ⟨u, hu, hqa⟩ := ha
    change wedge (a : Cochain) b ∈ relativeInvariants.map q
    refine ⟨wedge u b, invariant_wedge hu b.property.1, ?_⟩
    rw [q_wedge, hqa, LinearMap.mem_ker.mp b.property.2]
    simp [wedge]
  mul_right a b hb := by
    change (b : Cochain) ∈ relativeInvariants.map q at hb
    obtain ⟨v, hv, hqb⟩ := hb
    change wedge (a : Cochain) b ∈ relativeInvariants.map q
    refine ⟨wedge (cochainParity a) v,
      invariant_wedge (invariant_parity a.property.1) hv, ?_⟩
    rw [q_wedge, q_parity, LinearMap.mem_ker.mp a.property.2, map_zero,
      neg_zero, cochainParity_involutive, hqb]
    simp [wedge]
  translation_mem a ha := by
    change (a : Cochain) ∈ relativeInvariants.map q at ha
    obtain ⟨u, hu, hqa⟩ := ha
    change translation (a : Cochain) ∈ relativeInvariants.map q
    exact ⟨translation u, invariant_translation hu, by rw [hT u hu, hqa]⟩
  bracket_left a b n ha := by
    change (a : Cochain) ∈ relativeInvariants.map q at ha
    obtain ⟨u, hu, hqa⟩ := ha
    change br (a : Cochain) b n ∈ relativeInvariants.map q
    refine ⟨br u b n, hbr.invariant u b n hu b.property.1, ?_⟩
    rw [hbr.differential u b n hu b.property.1, hqa,
      LinearMap.mem_ker.mp b.property.2]
    simp
  bracket_right a b n hb := by
    change (b : Cochain) ∈ relativeInvariants.map q at hb
    obtain ⟨v, hv, hqb⟩ := hb
    change br (a : Cochain) b n ∈ relativeInvariants.map q
    refine ⟨br (cochainParity a) v n,
      hbr.invariant _ _ n (invariant_parity a.property.1) hv, ?_⟩
    rw [hbr.differential _ _ n (invariant_parity a.property.1) hv,
      q_parity, LinearMap.mem_ker.mp a.property.2, map_zero,
      neg_zero, cochainParity_involutive, hqb]
    simp

def data : DifferentialData Cohomology := (boundaries hT hbr).data

def bracket : LambdaBracket Cohomology := (boundaries hT hbr).bracket

theorem data_piece (d : Degree) : (data hT hbr).piece d = cohomologyPiece d := rfl

theorem isPVA (hC : IsPVA cochainData br) :
    IsPVA (data hT hbr) (bracket hT hbr) :=
  (boundaries hT hbr).isPVA cohomology_grading_internal
    ((cycles hT hbr).isPVA cycle_grading_internal hC)

theorem induced : IsInducedOnCohomology br (data hT hbr) (bracket hT hbr) where
  unit := ⟨one_mem_cycles, rfl⟩
  product _ _ hu hv := ⟨cycle_wedge hu hv, rfl⟩
  translation _ hu := ⟨cycle_translation hT hu, rfl⟩
  bracket _ _ hu hv n := ⟨cycle_bracket hbr hu hv n, rfl⟩
  grading d h := (cohomologyHomogeneous_iff_mem d h).symm

end CohomologyDescent
end KhanSL2
