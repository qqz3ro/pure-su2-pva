module

public import KhanSL2.BCFullBracketSkew
public import KhanSL2.BCFullAlgebra
public import KhanSL2.BCFullGrading

@[expose] public section

/-! The exact three degrees of every coefficient of the exterior `bc` bracket. -/

noncomputable section

namespace KhanSL2.FullBC

open LambdaPolynomial BC.PolynomialCalculus

theorem translation_pow_degree {d : Degree} {u : FullCochain}
    (hu : u ∈ fullPiece d) (n : ℕ) :
    (fullTranslation ^ n) u ∈ fullPiece (d + (0, 0, (n : ℤ))) := by
  induction n with
  | zero =>
    change u ∈ fullPiece (d + 0)
    simpa using hu
  | succ n hn =>
    simpa [pow_succ', Module.End.mul_apply, Nat.cast_add, add_assoc,
      Prod.mk_add_mk] using fullTranslation_degree hn

theorem translated_monomial_supercomm (s t : FullExteriorMonomial) (k : ℕ) :
    fullWedge (monomial s) ((fullTranslation ^ k) (monomial t)) =
      (-1 : ℂ) ^ (s.card * t.card) •
        fullWedge ((fullTranslation ^ k) (monomial t)) (monomial s) := by
  have hs := full_single_mem s 1
  have ht := translation_pow_degree (full_single_mem t 1) k
  have hsign : koszulSign (fullMonomialDegree s)
      (fullMonomialDegree t + (0, 0, (k : ℤ))) = (-1 : ℂ) ^ (s.card * t.card) := by
    rw [nat_parity_sign]
    simp only [koszulSign, fullMonomialDegree, Prod.fst_add, add_zero, Nat.cast_mul]
  simpa only [hsign] using full_supercomm hs ht

theorem wickTerm_degree (s t : FullExteriorMonomial) (m n : FullMode)
    (hm : m ∈ s) (hn : n ∈ t) (hp : m.pairsWith n) (j : ℕ) :
    wickTerm s t m n j ∈
      fullPiece ((fullMonomialDegree s).bracket (fullMonomialDegree t) j) := by
  simp only [wickTerm, mulRight_apply, K_apply, skew_single_apply]
  by_cases hj : j ≤ m.order + n.order
  · have hs := fullMonomialDegree_erase_add hm
    have ht := fullMonomialDegree_erase_add hn
    have hb : (m.bCount : ℤ) + (n.bCount : ℤ) = 1 := by
      exact_mod_cast FullMode.pairsWith_bCount m n hp
    have hw : (m.weight : ℤ) + (n.weight : ℤ) =
        (m.order : ℤ) + (n.order : ℤ) + 1 := by
      exact_mod_cast FullMode.pairsWith_weight m n hp
    have hd :
        (fullMonomialDegree (s.erase m) + (0, 0, ((m.order + n.order - j : ℕ) : ℤ))) +
          fullMonomialDegree (t.erase n) =
        (fullMonomialDegree s).bracket (fullMonomialDegree t) j := by
      rw [← hs, ← ht]
      ext <;> simp only [Degree.bracket, Prod.fst_add, Prod.snd_add,
        Prod.fst, Prod.snd, add_zero, zero_add] <;> omega
    have hmem := full_wedge_mem
      (translation_pow_degree (full_single_mem (s.erase m) 1)
        (m.order + n.order - j)) (full_single_mem (t.erase n) 1)
    rw [hd] at hmem
    change fullWedge (_ • _) _ ∈ _
    rw [show ∀ (r : ℂ) (a b : FullCochain), fullWedge (r • a) b = r • fullWedge a b from
      fun r a b => by simp [fullWedge, FiniteExterior.wedge]]
    exact (fullPiece _).smul_mem _ hmem
  · have hj' : m.order + n.order < j := by omega
    simp [Nat.choose_eq_zero_of_lt hj', fullData]

theorem monomialBracket_degree (s t : FullExteriorMonomial) (j : ℕ) :
    monomialBracket s t j ∈
      fullPiece ((fullMonomialDegree s).bracket (fullMonomialDegree t) j) := by
  rw [monomialBracket_eq_sum]
  simp only [Finset.sum_apply', Finsupp.smul_apply]
  apply (fullPiece _).sum_mem
  intro n hn
  apply (fullPiece _).sum_mem
  intro m hm
  by_cases h : kernelCoefficient n m = 0
  · simp [h]
  · apply (fullPiece _).smul_mem
    apply wickTerm_degree s t m n hm hn
    exact (FullMode.pairsWith_comm n m).mp (pairsWith_of_kernelCoefficient_ne_zero n m h)

theorem bracket_degree (d e : Degree) (a b : FullCochain) (j : ℕ)
    (ha : a ∈ fullPiece d) (hb : b ∈ fullPiece e) :
    bracket a b j ∈ fullPiece (d.bracket e j) := by
  rw [← a.sum_single, ← b.sum_single]
  simp only [Finsupp.sum, map_sum, LinearMap.sum_apply, bracket_single,
    Finset.sum_apply', Finsupp.smul_apply]
  apply (fullPiece _).sum_mem
  intro t ht
  apply (fullPiece _).sum_mem
  intro s hs
  apply (fullPiece _).smul_mem
  have hd : fullMonomialDegree s = d := ha hs
  have he : fullMonomialDegree t = e := hb ht
  simpa only [hd, he] using monomialBracket_degree s t j

end KhanSL2.FullBC

