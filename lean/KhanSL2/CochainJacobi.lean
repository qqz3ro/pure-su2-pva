module

public import KhanSL2.CochainGeneration
public import KhanSL2.Data
public import KhanSL2.JacobiLastPermutation

@[expose] public section

/-! Reduction of full CE super-Jacobi to the odd mode generators. -/

noncomputable section

namespace KhanSL2

open LambdaBracket

theorem cochain_bracket_one {br : LambdaBracket Cochain}
    (hL : HasSuperLeibniz cochainData br)
    {d : Degree} {a : Cochain} (ha : a ∈ cochainPiece d) :
    br a cochainOne = 0 := by
  apply Finsupp.ext
  intro n
  have h := superLeibniz_coeff hL ha cochain_one_mem cochainOne n
  change br a (wedge cochainOne cochainOne) n =
    wedge (br a cochainOne n) cochainOne +
      koszulSign d 0 • wedge cochainOne (br a cochainOne n) at h
  simp only [cochainOne_wedge, wedge_cochainOne, koszulSign_zero_right, one_smul] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

theorem cochain_jacobiator_one {br : LambdaBracket Cochain}
    (hL : HasSuperLeibniz cochainData br) (hdeg : HasBracketDegree cochainData br)
    {d e : Degree} {a b : Cochain} (ha : a ∈ cochainPiece d)
    (hb : b ∈ cochainPiece e) :
    jacobiator br (koszulSign d e) a b cochainOne = 0 := by
  have ha1 := cochain_bracket_one hL ha
  have hb1 := cochain_bracket_one hL hb
  have hab1 : ∀r : ℕ, br (br a b r) cochainOne = 0 :=
    fun r => cochain_bracket_one hL (hdeg _ _ _ _ r ha hb)
  rw [jacobiator_eq_zero_iff]
  simp [jacobiLeft, jacobiRight, jacobiMiddle, Finsupp.sum, ha1, hb1, hab1]

theorem cochain_jacobiator_third_of_generators {br : LambdaBracket Cochain}
    (hL : HasSuperLeibniz cochainData br) (hdeg : HasBracketDegree cochainData br)
    {d e : Degree} {a b : Cochain} (ha : a ∈ cochainPiece d)
    (hb : b ∈ cochainPiece e)
    (hgen : ∀m, jacobiator br (koszulSign d e) a b (generator m) = 0) :
    ∀c : Cochain, jacobiator br (koszulSign d e) a b c = 0 := by
  let J := jacobiator br (koszulSign d e) a b
  have h1 : J cochainOne = 0 := cochain_jacobiator_one hL hdeg ha hb
  have hp : ∀f c, c ∈ cochainPiece f → J c = 0 := by
    intro f c hc
    have h : c ∈ cochainPiece f ∧ J c = 0 := by
      apply cochain_homogeneous_induction
        (P := fun f c => c ∈ cochainPiece f ∧ J c = 0) _ _ _ _ _ hc
      · intro f
        exact ⟨(cochainPiece f).zero_mem, J.map_zero⟩
      · exact ⟨cochain_one_mem, h1⟩
      · intro f c c' hc hc'
        exact ⟨(cochainPiece f).add_mem hc.1 hc'.1,
          by rw [map_add, hc.2, hc'.2, add_zero]⟩
      · intro f r c hc
        exact ⟨(cochainPiece f).smul_mem r hc.1, by rw [map_smul, hc.2, smul_zero]⟩
      · intro f m c hc
        refine ⟨cochain_wedge_mem (cochain_generator_mem m) hc.1, ?_⟩
        change jacobiator br (koszulSign d e) a b (cochainData.mul (generator m) c) = 0
        rw [jacobiator_mul hL hdeg ha hb (cochain_generator_mem m)]
        change Finsupp.mapRange.linearMap _ (J (generator m)) +
          _ • Finsupp.mapRange.linearMap _ (J c) = 0
        rw [hgen m, hc.2, map_zero, map_zero, smul_zero, add_zero]
    exact h.2
  intro c
  have hc : c ∈ ⨆f, cochainPiece f := by
    rw [cochain_piece_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction cochainPiece (motive := fun c => J c = 0) hc
    (fun f c hc => hp f c hc) J.map_zero ?_
  intro c c' hc hc'
  rw [map_add, hc, hc', add_zero]

theorem cochain_jacobi_of_generators {br : LambdaBracket Cochain}
    (hL : HasSuperLeibniz cochainData br) (hdeg : HasBracketDegree cochainData br)
    (hR : HasSesquilinearRight translation br)
    (hT : HasSesquilinearLeft translation br)
    (hsk : HasSuperSkew cochainData br)
    (hgen : ∀i j k : Mode,
      jacobiator br (koszulSign (modeDegree i) (modeDegree j))
        (generator i) (generator j) (generator k) = 0)
    {d e : Degree} {a b : Cochain} (ha : a ∈ cochainPiece d)
    (hb : b ∈ cochainPiece e) (c : Cochain) :
    br.jacobiLeft a b c =
      br.jacobiMiddle a b c + koszulSign d e • br.jacobiRight a b c := by
  have hGG : ∀i j : Mode, ∀c : Cochain,
      jacobiator br (koszulSign (modeDegree i) (modeDegree j))
        (generator i) (generator j) c = 0 := by
    intro i j
    exact cochain_jacobiator_third_of_generators hL hdeg
      (cochain_generator_mem i) (cochain_generator_mem j) (hgen i j)
  have hG : ∀i : Mode, ∀e b, b ∈ cochainPiece e → ∀c : Cochain,
      jacobiator br (koszulSign (modeDegree i) e) (generator i) b c = 0 := by
    intro i e b hb
    apply cochain_jacobiator_third_of_generators hL hdeg (cochain_generator_mem i) hb
    intro k
    rw [jacobiator_lastSwap hR hsk hdeg (cochain_generator_mem i) hb
      (cochain_generator_mem k)]
    change -koszulSign e (modeDegree k) •
      lastSwap cochainData.translation
        (jacobiator br (koszulSign (modeDegree i) (modeDegree k))
          (generator i) (generator k) b) = 0
    rw [hGG i k, map_zero, smul_zero]
  have hbase : ∀i : Mode, jacobiator br (koszulSign d e) a b (generator i) = 0 := by
    intro i
    rw [jacobiator_lastSwap hR hsk hdeg ha hb (cochain_generator_mem i)]
    rw [jacobiator_swap hT hsk ha (cochain_generator_mem i)]
    change -koszulSign e (modeDegree i) •
      lastSwap cochainData.translation
        (-koszulSign d (modeDegree i) •
          swapVariables (jacobiator br (koszulSign (modeDegree i) d)
            (generator i) a b)) = 0
    rw [hG i d a ha b, map_zero, smul_zero, map_zero, smul_zero]
  exact (jacobiator_eq_zero_iff _ _ _ _ _).mp
    (cochain_jacobiator_third_of_generators hL hdeg ha hb hbase c)

end KhanSL2
