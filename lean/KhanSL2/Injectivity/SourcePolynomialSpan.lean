module

public import KhanSL2.Injectivity.AlternantProductSpan
public import KhanSL2.Injectivity.TaylorDiscriminant

@[expose] public section

noncomputable section

namespace KhanSL2.SourceDual

open Injectivity MvPolynomial

theorem taylorPolynomial_block_character (r s N : ℕ) (ell : Source →ₗ[ℂ] ℂ)
    (e : Equiv.Perm (Fin r)) (f : Equiv.Perm (Fin s)) :
    rename (Equiv.sumCongr e f) (taylorPolynomial r s N ell) =
      (f.sign : MvPolynomial (Variables r s) ℂ) * taylorPolynomial r s N ell := by
  have hcomp : (xPermutation e : Variables r s → Variables r s) ∘ yPermutation f =
      Equiv.sumCongr e f := by
    funext i
    cases i <;> rfl
  rw [← hcomp, ← rename_rename, taylorPolynomial_alternating_y, map_smul,
    taylorPolynomial_symmetric_x]
  rcases Int.units_eq_one_or f.sign with h | h <;> simp [h]

/-- The source relations force every testing polynomial into the explicit
polynomial span that the Newton chains must realize. -/
theorem taylorPolynomial_mem_cyclePolynomialSpan (r s N : ℕ)
    (ell : Source →ₗ[ℂ] ℂ) :
    taylorPolynomial r s N ell ∈ cyclePolynomialSpan r s := by
  obtain ⟨q, hq⟩ := exists_discriminant_quotient r s N ell
  have hs := discriminant_quotient_symmetric hq
    (taylorPolynomial_block_character r s N ell)
  rw [hq]
  exact discriminant_mul_mem_cyclePolynomialSpan r s q hs

end KhanSL2.SourceDual
