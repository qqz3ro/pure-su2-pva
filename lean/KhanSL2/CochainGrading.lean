module

public import KhanSL2.CE
public import KhanSL2.BasisGrading

@[expose] public section

/-! The actual direct-sum grading of the concrete finite CE cochains. -/

noncomputable section

namespace KhanSL2

theorem cochainPiece_eq_basisPiece (d : Degree) :
    cochainPiece d = BasisGrading.piece monomialDegree d := rfl

theorem cochain_grading_internal : DirectSum.IsInternal cochainPiece :=
  BasisGrading.isInternal monomialDegree

theorem cochain_piece_iSup_eq_top : (⨆ d, cochainPiece d) = ⊤ :=
  BasisGrading.piece_iSup_eq_top monomialDegree

def cochainProjection (d : Degree) : Module.End ℂ Cochain :=
  BasisGrading.projection monomialDegree d

@[simp] theorem cochainProjection_apply (d : Degree) (v : Cochain) (s : ExteriorMonomial) :
    cochainProjection d v s = if monomialDegree s = d then v s else 0 := rfl

theorem cochainProjection_mem (d : Degree) (v : Cochain) :
    cochainProjection d v ∈ cochainPiece d :=
  BasisGrading.projection_mem monomialDegree d v

theorem cochainProjection_of_mem {d : Degree} {v : Cochain} (hv : v ∈ cochainPiece d) :
    cochainProjection d v = v :=
  BasisGrading.projection_of_mem monomialDegree hv

theorem cochainProjection_of_mem_ne {d e : Degree} (hde : d ≠ e) {v : Cochain}
    (hv : v ∈ cochainPiece e) : cochainProjection d v = 0 :=
  BasisGrading.projection_of_mem_ne monomialDegree hde hv

theorem cochainProjection_linearMap (F : Module.End ℂ Cochain) (s : Degree)
    (hF : ∀ d v, v ∈ cochainPiece d → F v ∈ cochainPiece (d + s))
    (d : Degree) (v : Cochain) :
    cochainProjection (d + s) (F v) = F (cochainProjection d v) :=
  BasisGrading.projection_linearMap monomialDegree F (fun d => d + s)
    (fun _ _ h => add_right_cancel h) hF d v

theorem cochainHomogeneous_iff_mem (d : Degree) (v : Cochain) :
    cochainHomogeneous d v ↔ v ∈ cochainPiece d := Iff.rfl

theorem cochain_single_mem (s : ExteriorMonomial) (r : ℂ) :
    Finsupp.single s r ∈ cochainPiece (monomialDegree s) :=
  BasisGrading.single_mem monomialDegree s r

theorem cochain_one_mem : cochainOne ∈ cochainPiece 0 := by
  change cochainOne ∈ cochainPiece (0, 0, 0)
  simpa [cochainOne, monomialDegree] using cochain_single_mem ∅ 1

theorem cochain_generator_mem (m : Mode) :
    generator m ∈ cochainPiece (1, (m.bCount : ℤ), (m.weight : ℤ)) := by
  simpa [generator, monomialDegree] using cochain_single_mem {m} 1

theorem monomialDegree_union {s t : ExteriorMonomial} (h : Disjoint s t) :
    monomialDegree (s ∪ t) = monomialDegree s + monomialDegree t := by
  simp [monomialDegree, Finset.card_union_of_disjoint h, Finset.sum_union h,
    Nat.cast_add]

theorem monomialDegree_erase_add {m : Mode} {s : ExteriorMonomial} (hm : m ∈ s) :
    monomialDegree (s.erase m) + (1, (m.bCount : ℤ), (m.weight : ℤ)) =
      monomialDegree s := by
  have hcard := Finset.card_erase_add_one hm
  have hb := Finset.sum_erase_add (s := s) Mode.bCount hm
  have hs := Finset.sum_erase_add (s := s) Mode.weight hm
  ext <;> simp only [monomialDegree, Prod.fst_add, Prod.snd_add]
  · exact_mod_cast hcard
  · exact_mod_cast hb
  · exact_mod_cast hs

theorem monomialWedge_mem (s t : ExteriorMonomial) :
    monomialWedge s t ∈ cochainPiece (monomialDegree s + monomialDegree t) := by
  unfold monomialWedge
  split
  · rename_i h
    rw [← monomialDegree_union h]
    exact cochain_single_mem _ _
  · exact (cochainPiece _).zero_mem

theorem cochain_wedge_mem {d e : Degree} {u v : Cochain}
    (hu : u ∈ cochainPiece d) (hv : v ∈ cochainPiece e) :
    wedge u v ∈ cochainPiece (d + e) := by
  rw [← u.sum_single, ← v.sum_single]
  simp only [Finsupp.sum, wedge, map_sum, LinearMap.sum_apply]
  apply (cochainPiece _).sum_mem
  intro t ht
  apply (cochainPiece _).sum_mem
  intro s hs
  have hd : monomialDegree s = d := hu hs
  have he : monomialDegree t = e := hv ht
  simp only [wedgeLinear, Finsupp.linearCombination_single, LinearMap.smul_apply, smul_smul]
  apply (cochainPiece _).smul_mem
  simpa only [hd, he] using monomialWedge_mem s t

end KhanSL2
