module

public import KhanSL2.Macdonald.PolynomialFactorial

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Polynomial multiplication and differentiation are transposes for the
factorial pairing. These identities fix the normalization of symmetric
coefficient operators on restricted cochains. -/
noncomputable section
namespace KhanSL2.Macdonald

def polynomialPairing : Poly →ₗ[ℂ] Poly →ₗ[ℂ] ℂ :=
  (MvPolynomial.basisMonomials Mode ℂ).constr ℂ
    (fun d => (exponentFactorial d : ℂ) • MvPolynomial.lcoeff ℂ d)

@[simp] theorem polynomialPairing_monomial (d : Exponent) (p : Poly) :
    polynomialPairing (MvPolynomial.monomial d 1) p =
      (exponentFactorial d : ℂ) * p.coeff d := by
  change polynomialPairing ((MvPolynomial.basisMonomials Mode ℂ) d) p = _
  rw [polynomialPairing, Module.Basis.constr_basis]
  rfl

theorem polynomialPairing_symm (p q : Poly) : polynomialPairing p q = polynomialPairing q p := by
  have h : polynomialPairing = polynomialPairing.flip := by
    apply (MvPolynomial.basisMonomials Mode ℂ).ext
    intro d
    apply (MvPolynomial.basisMonomials Mode ℂ).ext
    intro e
    change polynomialPairing (MvPolynomial.monomial d 1) (MvPolynomial.monomial e 1) =
      polynomialPairing (MvPolynomial.monomial e 1) (MvPolynomial.monomial d 1)
    by_cases hde : d = e
    · subst e; rfl
    · simp [hde, Ne.symm hde]
  exact LinearMap.congr_fun (LinearMap.congr_fun h p) q

@[simp] theorem polynomialPairing_monomial_right (p : Poly) (d : Exponent) :
    polynomialPairing p (MvPolynomial.monomial d 1) =
      (exponentFactorial d : ℂ) * p.coeff d := by
  rw [polynomialPairing_symm, polynomialPairing_monomial]

/-- Multiplication by a polynomial variable is transpose to its partial derivative. -/
theorem polynomialPairing_X_mul (i : Mode) (p q : Poly) :
    polynomialPairing (MvPolynomial.X i * p) q = polynomialPairing p (MvPolynomial.pderiv i q) := by
  have hm (d : Exponent) :
      polynomialPairing (MvPolynomial.X i * MvPolynomial.monomial d 1) q =
        polynomialPairing (MvPolynomial.monomial d 1) (MvPolynomial.pderiv i q) := by
    rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul,
      add_comm (Finsupp.single i 1), polynomialPairing_monomial,
      polynomialPairing_monomial, MvPolynomial.coeff_pderiv, exponentFactorial_add_single]
    push_cast
    ring
  induction p using MvPolynomial.induction_on' with
  | add p r hp hr => simp only [mul_add, map_add, LinearMap.add_apply, hp, hr]
  | monomial d r =>
    have h : MvPolynomial.monomial d r = r • (MvPolynomial.monomial d (1 : ℂ)) := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [h, mul_smul_comm]
    simp only [map_smul, LinearMap.smul_apply, hm]


theorem polynomialPairing_pderiv (i : Mode) (p q : Poly) :
    polynomialPairing (MvPolynomial.pderiv i p) q = polynomialPairing p (MvPolynomial.X i * q) := by
  calc
    polynomialPairing (MvPolynomial.pderiv i p) q = polynomialPairing q (MvPolynomial.pderiv i p) := polynomialPairing_symm _ _
    _ = polynomialPairing (MvPolynomial.X i * q) p := (polynomialPairing_X_mul i q p).symm
    _ = polynomialPairing p (MvPolynomial.X i * q) := polynomialPairing_symm _ _

/-- Transposition reverses the two labels of a linear polynomial vector field. -/
theorem polynomialPairing_vectorField (i j : Mode) (p q : Poly) :
    polynomialPairing (MvPolynomial.X i * MvPolynomial.pderiv j p) q =
      polynomialPairing p (MvPolynomial.X j * MvPolynomial.pderiv i q) := by
  rw [polynomialPairing_X_mul, polynomialPairing_pderiv]

end KhanSL2.Macdonald
