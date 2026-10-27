module

public import KhanSL2.Injectivity.DiagonalFactors
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

/-! Determinantal form and permutation symmetry of the explicit discriminant. -/

noncomputable section

namespace KhanSL2.Injectivity

open MvPolynomial Finset

theorem orderedPair_prod {R : Type*} [CommMonoid R] {n : ℕ}
    (f : Fin n × Fin n → R) :
    (∏ a : OrderedPair n, f a.val) = ∏ i : Fin n, ∏ j ∈ Ioi i, f (i, j) := by
  rw [← Finset.prod_subtype (univ.filter (fun a : Fin n × Fin n => a.1 < a.2))
    (by simp) f, Finset.prod_filter, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  simp only [← Finset.prod_filter]
  congr 1
  ext j
  simp

def xVandermonde (r s : ℕ) : MvPolynomial (Fin r ⊕ Fin s) ℂ :=
  (Matrix.vandermonde (fun i : Fin r => (X (Sum.inl i) : MvPolynomial (Fin r ⊕ Fin s) ℂ))).det

def yVandermonde (r s : ℕ) : MvPolynomial (Fin r ⊕ Fin s) ℂ :=
  (Matrix.vandermonde (fun i : Fin s => (X (Sum.inr i) : MvPolynomial (Fin r ⊕ Fin s) ℂ))).det

def crossFactor (r s : ℕ) : MvPolynomial (Fin r ⊕ Fin s) ℂ :=
  ∏ i : Fin r, ∏ j : Fin s, (X (Sum.inl i) - X (Sum.inr j))

theorem discriminantFactor_eq (r s : ℕ) :
    discriminantFactor r s = xVandermonde r s ^ 2 * yVandermonde r s ^ 3 *
      crossFactor r s ^ 2 := by
  simp only [discriminantFactor, Fintype.prod_sum_type, diagonalFactor,
    diagonalEndpoints, diagonalMultiplicity]
  rw [Finset.prod_pow, Finset.prod_pow, Finset.prod_pow,
    orderedPair_prod (fun a : Fin r × Fin r => (X (Sum.inl a.2) - X (Sum.inl a.1) : MvPolynomial (Fin r ⊕ Fin s) ℂ)),
    orderedPair_prod (fun a : Fin s × Fin s => (X (Sum.inr a.2) - X (Sum.inr a.1) : MvPolynomial (Fin r ⊕ Fin s) ℂ)),
    Fintype.prod_prod_type]
  simp only [xVandermonde, yVandermonde, crossFactor, Matrix.det_vandermonde]
  ring

theorem rename_xVandermonde {r s : ℕ} (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)) :
    rename (Equiv.sumCongr e f) (xVandermonde r s) =
      (e.sign : MvPolynomial (Fin r ⊕ Fin s) ℂ) * xVandermonde r s := by
  rw [xVandermonde, AlgHom.map_det]
  convert Matrix.det_permute e
    (Matrix.vandermonde (fun i : Fin r => (X (Sum.inl i) : MvPolynomial (Fin r ⊕ Fin s) ℂ))) using 1
  congr 1
  ext i j
  simp [Matrix.vandermonde_apply]

theorem rename_yVandermonde {r s : ℕ} (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)) :
    rename (Equiv.sumCongr e f) (yVandermonde r s) =
      (f.sign : MvPolynomial (Fin r ⊕ Fin s) ℂ) * yVandermonde r s := by
  rw [yVandermonde, AlgHom.map_det]
  convert Matrix.det_permute f
    (Matrix.vandermonde (fun i : Fin s => (X (Sum.inr i) : MvPolynomial (Fin r ⊕ Fin s) ℂ))) using 1
  congr 1
  ext i j
  simp [Matrix.vandermonde_apply]

theorem rename_crossFactor {r s : ℕ} (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)) :
    rename (Equiv.sumCongr e f) (crossFactor r s) = crossFactor r s := by
  simp only [crossFactor, map_prod, map_sub, rename_X, Equiv.sumCongr_apply,
    Sum.map_inl, Sum.map_inr]
  calc
    _ = ∏ i : Fin r, ∏ j : Fin s, (X (Sum.inl i) - X (Sum.inr (f j))) := Equiv.prod_comp e _
    _ = _ := ?_
  apply Finset.prod_congr rfl
  intro i _
  exact Equiv.prod_comp f (fun j => (X (Sum.inl i) - X (Sum.inr j) : MvPolynomial (Fin r ⊕ Fin s) ℂ))

/-- The discriminant is symmetric in the X block and alternating in the Y block. -/
theorem rename_discriminantFactor {r s : ℕ}
    (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)) :
    rename (Equiv.sumCongr e f) (discriminantFactor r s) =
      (f.sign : MvPolynomial (Fin r ⊕ Fin s) ℂ) * discriminantFactor r s := by
  rw [discriminantFactor_eq]
  simp only [map_mul, map_pow, rename_xVandermonde, rename_yVandermonde, rename_crossFactor]
  rcases Int.units_eq_one_or e.sign with he | he <;>
    rcases Int.units_eq_one_or f.sign with hf | hf <;> simp [he, hf] <;> ring

/-- Dividing an alternating source polynomial by the complete factor leaves a block-symmetric polynomial. -/
theorem discriminant_quotient_symmetric {r s : ℕ} {p q : MvPolynomial (Fin r ⊕ Fin s) ℂ}
    (hp : p = discriminantFactor r s * q)
    (hs : ∀ (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)),
      rename (Equiv.sumCongr e f) p = (f.sign : MvPolynomial (Fin r ⊕ Fin s) ℂ) * p)
    (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)) :
    rename (Equiv.sumCongr e f) q = q := by
  apply rename_quotient_of_same_character (Equiv.sumCongr e f)
    (f.sign : MvPolynomial (Fin r ⊕ Fin s) ℂ) ?_ (discriminantFactor_ne_zero r s)
    hp (hs e f) (rename_discriminantFactor e f)
  rcases Int.units_eq_one_or f.sign with h | h <;> simp [h]

end KhanSL2.Injectivity
