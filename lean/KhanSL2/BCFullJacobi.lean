module

public import KhanSL2.BCFullGeneration
public import KhanSL2.JacobiLastPermutation

@[expose] public section

/-! Reduction of full CE super-Jacobi to the odd mode generators. -/

noncomputable section

namespace KhanSL2

open LambdaBracket

theorem full_bracket_one {br : LambdaBracket FullCochain}
    (hL : HasSuperLeibniz fullData br)
    {d : Degree} {a : FullCochain} (ha : a ∈ fullPiece d) :
    br a fullOne = 0 := by
  apply Finsupp.ext
  intro n
  have h := superLeibniz_coeff hL ha full_one_mem fullOne n
  change br a (fullWedge fullOne fullOne) n =
    fullWedge (br a fullOne n) fullOne +
      koszulSign d 0 • fullWedge fullOne (br a fullOne n) at h
  simp only [fullOne_wedge, fullWedge_one, koszulSign_zero_right, one_smul] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

theorem full_jacobiator_one {br : LambdaBracket FullCochain}
    (hL : HasSuperLeibniz fullData br) (hdeg : HasBracketDegree fullData br)
    {d e : Degree} {a b : FullCochain} (ha : a ∈ fullPiece d)
    (hb : b ∈ fullPiece e) :
    jacobiator br (koszulSign d e) a b fullOne = 0 := by
  have ha1 := full_bracket_one hL ha
  have hb1 := full_bracket_one hL hb
  have hab1 : ∀r : ℕ, br (br a b r) fullOne = 0 :=
    fun r => full_bracket_one hL (hdeg _ _ _ _ r ha hb)
  rw [jacobiator_eq_zero_iff]
  simp [jacobiLeft, jacobiRight, jacobiMiddle, Finsupp.sum, ha1, hb1, hab1]

theorem full_jacobiator_third_of_generators {br : LambdaBracket FullCochain}
    (hL : HasSuperLeibniz fullData br) (hdeg : HasBracketDegree fullData br)
    {d e : Degree} {a b : FullCochain} (ha : a ∈ fullPiece d)
    (hb : b ∈ fullPiece e)
    (hgen : ∀m, jacobiator br (koszulSign d e) a b (fullGenerator m) = 0) :
    ∀c : FullCochain, jacobiator br (koszulSign d e) a b c = 0 := by
  let J := jacobiator br (koszulSign d e) a b
  have h1 : J fullOne = 0 := full_jacobiator_one hL hdeg ha hb
  have hp : ∀f c, c ∈ fullPiece f → J c = 0 := by
    intro f c hc
    have h : c ∈ fullPiece f ∧ J c = 0 := by
      apply full_homogeneous_induction
        (P := fun f c => c ∈ fullPiece f ∧ J c = 0) _ _ _ _ _ hc
      · intro f
        exact ⟨(fullPiece f).zero_mem, J.map_zero⟩
      · exact ⟨full_one_mem, h1⟩
      · intro f c c' hc hc'
        exact ⟨(fullPiece f).add_mem hc.1 hc'.1,
          by rw [map_add, hc.2, hc'.2, add_zero]⟩
      · intro f r c hc
        exact ⟨(fullPiece f).smul_mem r hc.1, by rw [map_smul, hc.2, smul_zero]⟩
      · intro f m c hc
        refine ⟨full_wedge_mem (full_generator_mem m) hc.1, ?_⟩
        change jacobiator br (koszulSign d e) a b (fullData.mul (fullGenerator m) c) = 0
        rw [jacobiator_mul hL hdeg ha hb (full_generator_mem m)]
        change Finsupp.mapRange.linearMap _ (J (fullGenerator m)) +
          _ • Finsupp.mapRange.linearMap _ (J c) = 0
        rw [hgen m, hc.2, map_zero, map_zero, smul_zero, add_zero]
    exact h.2
  intro c
  have hc : c ∈ ⨆f, fullPiece f := by
    rw [full_piece_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction fullPiece (motive := fun c => J c = 0) hc
    (fun f c hc => hp f c hc) J.map_zero ?_
  intro c c' hc hc'
  rw [map_add, hc, hc', add_zero]

theorem full_jacobi_of_generators {br : LambdaBracket FullCochain}
    (hL : HasSuperLeibniz fullData br) (hdeg : HasBracketDegree fullData br)
    (hR : HasSesquilinearRight fullTranslation br)
    (hT : HasSesquilinearLeft fullTranslation br)
    (hsk : HasSuperSkew fullData br)
    (hgen : ∀i j k : FullMode,
      jacobiator br (koszulSign (fullModeDegree i) (fullModeDegree j))
        (fullGenerator i) (fullGenerator j) (fullGenerator k) = 0)
    {d e : Degree} {a b : FullCochain} (ha : a ∈ fullPiece d)
    (hb : b ∈ fullPiece e) (c : FullCochain) :
    br.jacobiLeft a b c =
      br.jacobiMiddle a b c + koszulSign d e • br.jacobiRight a b c := by
  have hGG : ∀i j : FullMode, ∀c : FullCochain,
      jacobiator br (koszulSign (fullModeDegree i) (fullModeDegree j))
        (fullGenerator i) (fullGenerator j) c = 0 := by
    intro i j
    exact full_jacobiator_third_of_generators hL hdeg
      (full_generator_mem i) (full_generator_mem j) (hgen i j)
  have hG : ∀i : FullMode, ∀e b, b ∈ fullPiece e → ∀c : FullCochain,
      jacobiator br (koszulSign (fullModeDegree i) e) (fullGenerator i) b c = 0 := by
    intro i e b hb
    apply full_jacobiator_third_of_generators hL hdeg (full_generator_mem i) hb
    intro k
    rw [jacobiator_lastSwap hR hsk hdeg (full_generator_mem i) hb
      (full_generator_mem k)]
    change -koszulSign e (fullModeDegree k) •
      lastSwap fullData.translation
        (jacobiator br (koszulSign (fullModeDegree i) (fullModeDegree k))
          (fullGenerator i) (fullGenerator k) b) = 0
    rw [hGG i k, map_zero, smul_zero]
  have hbase : ∀i : FullMode, jacobiator br (koszulSign d e) a b (fullGenerator i) = 0 := by
    intro i
    rw [jacobiator_lastSwap hR hsk hdeg ha hb (full_generator_mem i)]
    rw [jacobiator_swap hT hsk ha (full_generator_mem i)]
    change -koszulSign e (fullModeDegree i) •
      lastSwap fullData.translation
        (-koszulSign d (fullModeDegree i) •
          swapVariables (jacobiator br (koszulSign (fullModeDegree i) d)
            (fullGenerator i) a b)) = 0
    rw [hG i d a ha b, map_zero, smul_zero, map_zero, smul_zero]
  exact (jacobiator_eq_zero_iff _ _ _ _ _).mp
    (full_jacobiator_third_of_generators hL hdeg ha hb hbase c)

end KhanSL2
