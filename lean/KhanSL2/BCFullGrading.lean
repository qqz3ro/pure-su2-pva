module

public import KhanSL2.BCFullCE

@[expose] public section

/-! The finite direct-sum grading with zero ghosts included. -/

noncomputable section

namespace KhanSL2

def fullMonomialWedge := FiniteExterior.monomialWedge FullMode.code

theorem full_grading_internal : DirectSum.IsInternal fullPiece :=
  BasisGrading.isInternal fullMonomialDegree

theorem full_piece_iSup_eq_top : (⨆ d, fullPiece d) = ⊤ :=
  BasisGrading.piece_iSup_eq_top fullMonomialDegree

theorem full_single_mem (s : FullExteriorMonomial) (r : ℂ) :
    Finsupp.single s r ∈ fullPiece (fullMonomialDegree s) :=
  BasisGrading.single_mem fullMonomialDegree s r

theorem full_one_mem : fullOne ∈ fullPiece 0 := by
  change fullOne ∈ fullPiece (0, 0, 0)
  simpa [fullOne, FiniteExterior.monomial, fullMonomialDegree] using full_single_mem ∅ 1

theorem full_generator_mem (m : FullMode) :
    fullGenerator m ∈ fullPiece (1, (m.bCount : ℤ), (m.weight : ℤ)) := by
  simpa [fullGenerator, FiniteExterior.generator, FiniteExterior.monomial, fullMonomialDegree] using
    full_single_mem {m} 1

theorem fullMonomialDegree_union {s t : FullExteriorMonomial} (h : Disjoint s t) :
    fullMonomialDegree (s ∪ t) = fullMonomialDegree s + fullMonomialDegree t := by
  simp [fullMonomialDegree, Finset.card_union_of_disjoint h, Finset.sum_union h,
    Nat.cast_add]

theorem fullMonomialDegree_erase_add {m : FullMode} {s : FullExteriorMonomial}
    (hm : m ∈ s) :
    fullMonomialDegree (s.erase m) + (1, (m.bCount : ℤ), (m.weight : ℤ)) =
      fullMonomialDegree s := by
  have hcard := Finset.card_erase_add_one hm
  have hb := Finset.sum_erase_add (s := s) FullMode.bCount hm
  have hs := Finset.sum_erase_add (s := s) FullMode.weight hm
  ext <;> simp only [fullMonomialDegree, Prod.fst_add, Prod.snd_add]
  · exact_mod_cast hcard
  · exact_mod_cast hb
  · exact_mod_cast hs

theorem fullMonomialWedge_mem (s t : FullExteriorMonomial) :
    fullMonomialWedge s t ∈ fullPiece (fullMonomialDegree s + fullMonomialDegree t) := by
  unfold fullMonomialWedge FiniteExterior.monomialWedge
  split
  · rename_i h
    rw [← fullMonomialDegree_union h]
    exact full_single_mem _ _
  · exact (fullPiece _).zero_mem

theorem full_wedge_mem {d e : Degree} {u v : FullCochain}
    (hu : u ∈ fullPiece d) (hv : v ∈ fullPiece e) :
    fullWedge u v ∈ fullPiece (d + e) := by
  rw [← u.sum_single, ← v.sum_single]
  simp only [Finsupp.sum, fullWedge, FiniteExterior.wedge, map_sum, LinearMap.sum_apply]
  apply (fullPiece _).sum_mem
  intro t ht
  apply (fullPiece _).sum_mem
  intro s hs
  have hd : fullMonomialDegree s = d := hu hs
  have he : fullMonomialDegree t = e := hv ht
  simp only [FiniteExterior.wedgeLinear, Finsupp.linearCombination_single,
    LinearMap.smul_apply, smul_smul]
  apply (fullPiece _).smul_mem
  simpa only [hd, he, fullMonomialWedge] using fullMonomialWedge_mem s t

theorem fullExtendDerivation_degree (f : FullMode → FullCochain) (δ : Degree)
    (hf : ∀m, f m ∈ fullPiece ((1, (m.bCount : ℤ), (m.weight : ℤ)) + δ))
    {d : Degree} {u : FullCochain} (hu : u ∈ fullPiece d) :
    FiniteExterior.extendDerivation FullMode.code f u ∈ fullPiece (d + δ) := by
  rw [← u.sum_single]
  simp only [Finsupp.sum, map_sum, FiniteExterior.extendDerivation,
    Finsupp.linearCombination_single]
  apply (fullPiece _).sum_mem
  intro s hs
  apply (fullPiece _).smul_mem
  apply (fullPiece _).sum_mem
  intro m hm
  apply (fullPiece _).smul_mem
  have hd : fullMonomialDegree s = d := hu hs
  have herase := fullMonomialDegree_erase_add hm
  have heq : ((1, (m.bCount : ℤ), (m.weight : ℤ)) + δ) +
      fullMonomialDegree (s.erase m) = d + δ := by
    rw [← hd, ← herase]
    ac_rfl
  rw [← heq]
  exact full_wedge_mem (hf m) (full_single_mem _ 1)

theorem fullTranslationGenerator_degree (m : FullMode) :
    fullTranslationGenerator m ∈ fullPiece
      ((1, (m.bCount : ℤ), (m.weight : ℤ)) + (0, 0, 1)) := by
  apply (fullPiece _).smul_mem
  simpa using full_generator_mem m.next

theorem fullTranslation_degree {d : Degree} {u : FullCochain} (hu : u ∈ fullPiece d) :
    fullTranslation u ∈ fullPiece (d + (0, 0, 1)) :=
  fullExtendDerivation_degree fullTranslationGenerator (0, 0, 1)
    fullTranslationGenerator_degree hu

end KhanSL2
