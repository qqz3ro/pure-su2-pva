module

public import KhanSL2.BCBracketSkew
public import KhanSL2.CEDegrees
public import KhanSL2.CochainSupercomm

@[expose] public section

/-! The exact three degrees of every coefficient of the exterior `bc` bracket. -/

noncomputable section

namespace KhanSL2.BC

open LambdaPolynomial PolynomialCalculus

theorem translation_pow_degree {d : Degree} {u : Cochain}
    (hu : u ∈ cochainPiece d) (n : ℕ) :
    (translation ^ n) u ∈ cochainPiece (d + (0, 0, (n : ℤ))) := by
  induction n with
  | zero =>
    change u ∈ cochainPiece (d + 0)
    simpa using hu
  | succ n hn =>
    simpa [pow_succ', Module.End.mul_apply, Nat.cast_add, add_assoc,
      Prod.mk_add_mk] using translation_degree hn

theorem translated_monomial_supercomm (s t : ExteriorMonomial) (k : ℕ) :
    wedge (monomial s) ((translation ^ k) (monomial t)) =
      (-1 : ℂ) ^ (s.card * t.card) •
        wedge ((translation ^ k) (monomial t)) (monomial s) := by
  have hs := cochain_single_mem s 1
  have ht := translation_pow_degree (cochain_single_mem t 1) k
  have hsign : koszulSign (monomialDegree s)
      (monomialDegree t + (0, 0, (k : ℤ))) = (-1 : ℂ) ^ (s.card * t.card) := by
    rw [nat_parity_sign]
    simp only [koszulSign, monomialDegree, Prod.fst_add, add_zero, Nat.cast_mul]
  simpa only [hsign] using cochain_supercomm hs ht

theorem wickTerm_degree (s t : ExteriorMonomial) (m n : Mode)
    (hm : m ∈ s) (hn : n ∈ t) (hp : m.pairsWith n) (j : ℕ) :
    wickTerm s t m n j ∈
      cochainPiece ((monomialDegree s).bracket (monomialDegree t) j) := by
  simp only [wickTerm, mulRight_apply, K_apply, skew_single_apply]
  by_cases hj : j ≤ m.order + n.order
  · have hs := monomialDegree_erase_add hm
    have ht := monomialDegree_erase_add hn
    have hb : (m.bCount : ℤ) + (n.bCount : ℤ) = 1 := by
      exact_mod_cast Mode.pairsWith_bCount m n hp
    have hw : (m.weight : ℤ) + (n.weight : ℤ) =
        (m.order : ℤ) + (n.order : ℤ) + 1 := by
      exact_mod_cast Mode.pairsWith_weight m n hp
    have hd :
        (monomialDegree (s.erase m) + (0, 0, ((m.order + n.order - j : ℕ) : ℤ))) +
          monomialDegree (t.erase n) =
        (monomialDegree s).bracket (monomialDegree t) j := by
      rw [← hs, ← ht]
      ext <;> simp only [Degree.bracket, Prod.fst_add, Prod.snd_add,
        Prod.fst, Prod.snd, add_zero, zero_add] <;> omega
    have hmem := cochain_wedge_mem
      (translation_pow_degree (cochain_single_mem (s.erase m) 1)
        (m.order + n.order - j)) (cochain_single_mem (t.erase n) 1)
    rw [hd] at hmem
    change wedge (_ • _) _ ∈ _
    rw [show ∀ (r : ℂ) (a b : Cochain), wedge (r • a) b = r • wedge a b from
      fun r a b => by simp [wedge]]
    exact (cochainPiece _).smul_mem _ hmem
  · have hj' : m.order + n.order < j := by omega
    simp [Nat.choose_eq_zero_of_lt hj', cochainData]

theorem monomialBracket_degree (s t : ExteriorMonomial) (j : ℕ) :
    monomialBracket s t j ∈
      cochainPiece ((monomialDegree s).bracket (monomialDegree t) j) := by
  rw [monomialBracket_eq_sum]
  simp only [Finset.sum_apply', Finsupp.smul_apply]
  apply (cochainPiece _).sum_mem
  intro n hn
  apply (cochainPiece _).sum_mem
  intro m hm
  by_cases h : kernelCoefficient n m = 0
  · simp [h]
  · apply (cochainPiece _).smul_mem
    apply wickTerm_degree s t m n hm hn
    exact (Mode.pairsWith_comm n m).mp (pairsWith_of_kernelCoefficient_ne_zero n m h)

theorem bracket_degree (d e : Degree) (a b : Cochain) (j : ℕ)
    (ha : a ∈ cochainPiece d) (hb : b ∈ cochainPiece e) :
    bracket a b j ∈ cochainPiece (d.bracket e j) := by
  rw [← a.sum_single, ← b.sum_single]
  simp only [Finsupp.sum, map_sum, LinearMap.sum_apply, bracket_single,
    Finset.sum_apply', Finsupp.smul_apply]
  apply (cochainPiece _).sum_mem
  intro t ht
  apply (cochainPiece _).sum_mem
  intro s hs
  apply (cochainPiece _).smul_mem
  have hd : monomialDegree s = d := ha hs
  have he : monomialDegree t = e := hb ht
  simpa only [hd, he] using monomialBracket_degree s t j

end KhanSL2.BC
