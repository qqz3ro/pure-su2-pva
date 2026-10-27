module

public import KhanSL2.SourceAlgebra
public import KhanSL2.JacobiTranslation

@[expose] public section

/-!
# Extending Jacobi from the two source generators in its third argument

No Jacobi identity is assumed for arbitrary arguments. The result uses the
proved source differential generation and the independently proved product
and translation rules for the Jacobiator.
-/

noncomputable section

namespace KhanSL2.Source

open LambdaBracket

theorem bracket_one_of_mem {br : LambdaBracket Source}
    (hL : HasSuperLeibniz sourceData br) {d : Degree} {a : Source}
    (ha : a ∈ piece d) : br a 1 = 0 := by
  ext n
  have h := superLeibniz_coeff hL ha one_mem (1 : Source) n
  change br a (1 * 1) n = br a 1 n * 1 + koszulSign d 0 • (1 * br a 1 n) at h
  simp only [one_mul, mul_one, koszulSign_zero_right, one_smul] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

theorem jacobiator_one {br : LambdaBracket Source}
    (hL : HasSuperLeibniz sourceData br) (hdeg : HasBracketDegree sourceData br)
    {d e : Degree} {a b : Source} (ha : a ∈ piece d) (hb : b ∈ piece e) :
    jacobiator br (koszulSign d e) a b 1 = 0 := by
  have ha1 := bracket_one_of_mem hL ha
  have hb1 := bracket_one_of_mem hL hb
  have hab1 : ∀ r : ℕ, br (br a b r) 1 = 0 :=
    fun r => bracket_one_of_mem hL (hdeg _ _ _ _ r ha hb)
  rw [jacobiator_eq_zero_iff]
  simp [jacobiLeft, jacobiRight, jacobiMiddle, Finsupp.sum, ha1, hb1, hab1]

/-- With the first two homogeneous arguments fixed, it suffices to check
Jacobi on `X 0` and `Y 0` in the third argument. -/
theorem jacobiator_third_of_generators {br : LambdaBracket Source}
    (hL : HasSuperLeibniz sourceData br) (hdeg : HasBracketDegree sourceData br)
    (hR : HasSesquilinearRight translation br)
    {d e : Degree} {a b : Source} (ha : a ∈ piece d) (hb : b ∈ piece e)
    (hx : jacobiator br (koszulSign d e) a b (X 0) = 0)
    (hy : jacobiator br (koszulSign d e) a b (Y 0) = 0) :
    ∀ c : Source, jacobiator br (koszulSign d e) a b c = 0 := by
  let J := jacobiator br (koszulSign d e) a b
  have h1 : J 1 = 0 := jacobiator_one hL hdeg ha hb
  have hp : ∀ f c, c ∈ piece f → J c = 0 := by
    intro f c hc
    have h : c ∈ piece f ∧ J c = 0 := by
      apply homogeneous_induction (P := fun f c => c ∈ piece f ∧ J c = 0)
        _ _ _ _ _ _ _ hc
      · intro f
        exact ⟨(piece f).zero_mem, J.map_zero⟩
      · intro r
        refine ⟨⟨.ofScalar r, .scalar r, rfl⟩, ?_⟩
        rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
      · exact ⟨X_mem 0, hx⟩
      · exact ⟨Y_mem 0, hy⟩
      · intro f c c' hc hc'
        exact ⟨(piece f).add_mem hc.1 hc'.1, by rw [map_add, hc.2, hc'.2, add_zero]⟩
      · intro f g c c' hc hc'
        refine ⟨mul_mem hc.1 hc'.1, ?_⟩
        change jacobiator br (koszulSign d e) a b (sourceData.mul c c') = 0
        rw [jacobiator_mul hL hdeg ha hb hc.1]
        change Finsupp.mapRange.linearMap _ (J c) +
          _ • Finsupp.mapRange.linearMap _ (J c') = 0
        rw [hc.2, hc'.2, map_zero, map_zero, smul_zero, add_zero]
      · intro f c hc
        refine ⟨translation_mem hc.1, ?_⟩
        change jacobiator br (koszulSign d e) a b (translation c) = 0
        rw [jacobiator_translation hR]
        change jacobiTranslation translation (J c) = 0
        rw [hc.2, map_zero]
    exact h.2
  intro c
  have hc : c ∈ ⨆ f, piece f := by
    rw [piece_iSup_eq_top]
    trivial
  refine Submodule.iSup_induction piece (motive := fun c => J c = 0) hc
    (fun f c hc => hp f c hc) J.map_zero ?_
  intro c c' hc hc'
  rw [map_add, hc, hc', add_zero]

end KhanSL2.Source
