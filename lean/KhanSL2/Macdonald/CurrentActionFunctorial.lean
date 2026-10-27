module

public import KhanSL2.Macdonald.CurrentAction

@[expose] public section

/-! Polynomial derivation compatibility is determined by the actual variables. -/

noncomputable section
namespace KhanSL2.Macdonald

theorem polynomialDerivation_intertwines {A : Type*} [CommRing A] [Algebra ℂ A]
    (f : Poly →ₐ[ℂ] A) (D : Derivation ℂ Poly Poly) (E : Derivation ℂ A A)
    (hX : ∀ m : Mode, f (D (MvPolynomial.X m)) = E (f (MvPolynomial.X m))) (p : Poly) :
    f (D p) = E (f p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.derivation_C, map_zero]
    change (0 : A) = E (f (algebraMap ℂ Poly c))
    rw [AlgHom.commutes, Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p m hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hX]

end KhanSL2.Macdonald
