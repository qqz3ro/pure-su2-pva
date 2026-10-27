module

public import KhanSL2.Injectivity.VandermondeFactors
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

noncomputable section
open Finset

namespace KhanSL2.Injectivity

theorem det_vandermonde_all_pairs {R : Type*} [CommRing R] {n : ℕ} (z : Fin n → R) :
    (Matrix.vandermonde z).det = ∏ i : Fin n, ∏ j : Fin n, if i < j then z j - z i else 1 := by
  rw [Matrix.det_vandermonde]
  apply prod_congr rfl
  intro i _
  rw [← prod_filter]
  congr 1
  ext j
  simp

/-- Concatenating alphabets factors the Vandermonde into its two diagonal blocks
and the full cross product. This includes either empty alphabet. -/
theorem det_vandermonde_append {R : Type*} [CommRing R] {r s : ℕ}
    (z : Fin r → R) (w : Fin s → R) :
    (Matrix.vandermonde (Fin.append z w)).det =
      (Matrix.vandermonde z).det * (Matrix.vandermonde w).det *
        ∏ i : Fin r, ∏ j : Fin s, (w j - z i) := by
  classical
  simp only [det_vandermonde_all_pairs]
  rw [Fin.prod_univ_add]
  have hleft (i : Fin r) :
      (∏ j : Fin (r + s), if Fin.castAdd s i < j then
        Fin.append z w j - Fin.append z w (Fin.castAdd s i) else 1) =
      (∏ j : Fin r, if i < j then z j - z i else 1) * ∏ j : Fin s, (w j - z i) := by
    rw [Fin.prod_univ_add]
    congr 1
    · apply prod_congr rfl
      intro j _
      simp only [Fin.append_left, Fin.append_right, Fin.lt_def, Fin.val_castAdd,
        Fin.val_natAdd, Nat.add_lt_add_iff_left]
    · apply prod_congr rfl
      intro j _
      have h : Fin.castAdd s i < Fin.natAdd r j := by
        simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
        omega
      simp [h]
  have hright (i : Fin s) :
      (∏ j : Fin (r + s), if Fin.natAdd r i < j then
        Fin.append z w j - Fin.append z w (Fin.natAdd r i) else 1) =
      ∏ j : Fin s, if i < j then w j - w i else 1 := by
    rw [Fin.prod_univ_add]
    have hz : (∏ j : Fin r, if Fin.natAdd r i < Fin.castAdd s j then
        Fin.append z w (Fin.castAdd s j) - Fin.append z w (Fin.natAdd r i) else 1) = 1 := by
      apply prod_eq_one
      intro j _
      have h : ¬ Fin.natAdd r i < Fin.castAdd s j := by
        simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
        omega
      simp [h]
    rw [hz, one_mul]
    apply prod_congr rfl
    intro j _
    simp only [Fin.append_left, Fin.append_right, Fin.lt_def, Fin.val_castAdd,
        Fin.val_natAdd, Nat.add_lt_add_iff_left]
  simp only [hleft, hright, prod_mul_distrib]
  ring

theorem crossFactor_reverse (r s : ℕ) :
    (∏ i : Fin r, ∏ j : Fin s,
      (MvPolynomial.X (Sum.inr j) - MvPolynomial.X (Sum.inl i) :
        MvPolynomial (Fin r ⊕ Fin s) ℂ)) =
      (-1 : MvPolynomial (Fin r ⊕ Fin s) ℂ) ^ (r * s) * crossFactor r s := by
  have hpair (i : Fin r) (j : Fin s) :
      (MvPolynomial.X (Sum.inr j) - MvPolynomial.X (Sum.inl i) :
        MvPolynomial (Fin r ⊕ Fin s) ℂ) =
      -1 * (MvPolynomial.X (Sum.inl i) - MvPolynomial.X (Sum.inr j)) := by ring
  simp only [hpair, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, crossFactor]
  rw [← pow_mul, Nat.mul_comm s r]

/-- The neutral determinant in the polynomial coordinates used by the source. -/
theorem neutral_vandermonde (r s : ℕ) :
    (Matrix.vandermonde (Fin.append
      (fun i : Fin r => (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin r ⊕ Fin s) ℂ))
      (fun j : Fin s => MvPolynomial.X (Sum.inr j)))).det =
      (-1 : MvPolynomial (Fin r ⊕ Fin s) ℂ) ^ (r * s) *
        xVandermonde r s * yVandermonde r s * crossFactor r s := by
  rw [det_vandermonde_append, crossFactor_reverse]
  change xVandermonde r s * yVandermonde r s *
    ((-1 : MvPolynomial (Fin r ⊕ Fin s) ℂ) ^ (r * s) * crossFactor r s) = _
  ring

end KhanSL2.Injectivity
