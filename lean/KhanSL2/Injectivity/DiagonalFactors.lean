module

public import KhanSL2.Injectivity.DiagonalDivisibility

@[expose] public section

/-! The explicit discriminant factor in the source functional polynomial. -/

noncomputable section

namespace KhanSL2.Injectivity

open MvPolynomial

abbrev OrderedPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- The three kinds of diagonals: XX, YY, and XY. -/
abbrev DiagonalIndex (r s : ℕ) := OrderedPair r ⊕ OrderedPair s ⊕ (Fin r × Fin s)

def diagonalEndpoints {r s : ℕ} : DiagonalIndex r s →
    (Fin r ⊕ Fin s) × (Fin r ⊕ Fin s)
  | Sum.inl p => (Sum.inl p.val.2, Sum.inl p.val.1)
  | Sum.inr (Sum.inl p) => (Sum.inr p.val.2, Sum.inr p.val.1)
  | Sum.inr (Sum.inr p) => (Sum.inl p.1, Sum.inr p.2)

def diagonalMultiplicity {r s : ℕ} : DiagonalIndex r s → ℕ
  | Sum.inl _ => 2
  | Sum.inr (Sum.inl _) => 3
  | Sum.inr (Sum.inr _) => 2

def diagonalFactor {r s : ℕ} (a : DiagonalIndex r s) : MvPolynomial (Fin r ⊕ Fin s) ℂ :=
  X (diagonalEndpoints a).1 - X (diagonalEndpoints a).2

/-- `Δ(z)^2 Δ(w)^3 ∏ (z_i-w_a)^2`, with the increasing Vandermonde convention. -/
def discriminantFactor (r s : ℕ) : MvPolynomial (Fin r ⊕ Fin s) ℂ :=
  ∏ a : DiagonalIndex r s, diagonalFactor a ^ diagonalMultiplicity a

theorem diagonalEndpoints_ne {r s : ℕ} (a : DiagonalIndex r s) :
    (diagonalEndpoints a).1 ≠ (diagonalEndpoints a).2 := by
  rcases a with a | a | a
  · simpa [diagonalEndpoints] using a.property.ne'
  · simpa [diagonalEndpoints] using a.property.ne'
  · simp [diagonalEndpoints]

theorem diagonalEndpoints_injective {r s : ℕ} :
    Function.Injective (diagonalEndpoints (r := r) (s := s)) := by
  intro a b h
  rcases a with a | a | a <;> rcases b with b | b | b
  all_goals simp only [diagonalEndpoints, Prod.mk.injEq, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, false_and, and_false] at h
  · congr 1
    apply Subtype.ext
    exact Prod.ext h.2 h.1
  · congr 2
    apply Subtype.ext
    exact Prod.ext h.2 h.1
  · congr 2
    exact Prod.ext h.1 h.2

theorem diagonalEndpoints_not_reverse {r s : ℕ} (a b : DiagonalIndex r s) :
    diagonalEndpoints a ≠ ((diagonalEndpoints b).2, (diagonalEndpoints b).1) := by
  intro h
  rcases a with a | a | a <;> rcases b with b | b | b
  all_goals simp only [diagonalEndpoints, Prod.mk.injEq, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq, false_and, and_false] at h
  · have ha := a.property
    have hb := b.property
    rw [h.1, h.2] at ha
    exact (lt_asymm ha hb).elim
  · have ha := a.property
    have hb := b.property
    rw [h.1, h.2] at ha
    exact (lt_asymm ha hb).elim

theorem diagonalFactor_ne_zero {r s : ℕ} (a : DiagonalIndex r s) :
    diagonalFactor a ≠ 0 := by
  apply sub_ne_zero.mpr
  exact fun h => diagonalEndpoints_ne a (MvPolynomial.X_injective h)

theorem discriminantFactor_ne_zero (r s : ℕ) : discriminantFactor r s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  exact pow_ne_zero _ (diagonalFactor_ne_zero a)

/-- All required local multiplicities imply divisibility by the complete factor. -/
theorem discriminantFactor_dvd {r s : ℕ} (p : MvPolynomial (Fin r ⊕ Fin s) ℂ)
    (h : ∀ a : DiagonalIndex r s, diagonalFactor a ^ diagonalMultiplicity a ∣ p) :
    discriminantFactor r s ∣ p := by
  apply Fintype.prod_dvd_of_isRelPrime ?_ h
  intro a b hab
  apply IsRelPrime.pow
  apply diagonal_isRelPrime (diagonalEndpoints_ne a) (diagonalEndpoints_ne b)
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · exact hab (diagonalEndpoints_injective (Prod.ext h₁.symm h₂.symm))
  · exact diagonalEndpoints_not_reverse a b (Prod.ext h₂.symm h₁.symm)

/-- Source symmetry and diagonal vanishing produce the manuscript's exact divisor. -/
theorem discriminantFactor_dvd_of_diagonals {r s : ℕ}
    (p : MvPolynomial (Fin r ⊕ Fin s) ℂ)
    (hxx : ∀ i j : Fin r, i ≠ j →
      diagonal (Sum.inl i) (Sum.inl j) p = 0 ∧
      rename (Equiv.swap (Sum.inl i) (Sum.inl j)) p = p)
    (hyy : ∀ i j : Fin s, i ≠ j →
      rename (Equiv.swap (Sum.inr i) (Sum.inr j)) p = -p ∧
      diagonal (Sum.inr i) (Sum.inr j) (pderiv (Sum.inr i) p) = 0)
    (hxy : ∀ (i : Fin r) (j : Fin s),
      diagonal (Sum.inl i) (Sum.inr j) p = 0 ∧
      diagonal (Sum.inl i) (Sum.inr j) (pderiv (Sum.inl i) p) = 0) :
    discriminantFactor r s ∣ p := by
  apply discriminantFactor_dvd
  rintro (a | a | a)
  · exact diagonal_sq_dvd_of_symmetric (diagonalEndpoints_ne (r := r) (s := s) (Sum.inl a)) p
      (hxx _ _ a.property.ne').1 (hxx _ _ a.property.ne').2
  · exact diagonal_cube_dvd_of_antisymmetric (diagonalEndpoints_ne (r := r) (s := s) (Sum.inr (Sum.inl a))) p
      (hyy _ _ a.property.ne').1 (hyy _ _ a.property.ne').2
  · exact diagonal_sq_dvd (diagonalEndpoints_ne (r := r) (s := s) (Sum.inr (Sum.inr a))) p (hxy a.1 a.2).1 (hxy a.1 a.2).2

/-- Cancellation of a common permutation character makes the quotient invariant. -/
theorem rename_quotient_of_same_character {σ : Type*} {p f q : MvPolynomial σ ℂ}
    (e : Equiv.Perm σ) (c : MvPolynomial σ ℂ) (hc : c ≠ 0) (hf : f ≠ 0)
    (hp : p = f * q) (heP : rename e p = c * p) (heF : rename e f = c * f) :
    rename e q = q := by
  rw [hp, map_mul, heF, ← mul_assoc] at heP
  exact mul_left_cancel₀ (mul_ne_zero hc hf) heP

end KhanSL2.Injectivity
