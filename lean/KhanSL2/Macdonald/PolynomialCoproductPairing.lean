module

public import KhanSL2.Macdonald.PolynomialPairing
public import KhanSL2.Macdonald.SymmetricCoefficientsCoproduct

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The factorial pairing identifies polynomial multiplication with the
actual primitive coproduct on symmetric current coefficients. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

def polynomialTensorPairing (p q : Poly) :
    SymmetricCoefficients ⊗[ℂ] SymmetricCoefficients →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((polynomialPairing p).smulRight (polynomialPairing q))

@[simp] theorem polynomialTensorPairing_tmul (p q r s : Poly) :
    polynomialTensorPairing p q
      ((show SymmetricCoefficients from r) ⊗ₜ[ℂ] (show SymmetricCoefficients from s)) =
        polynomialPairing p r * polynomialPairing q s := rfl

@[simp] theorem polynomialPairing_one_right (p : Poly) :
    polynomialPairing p 1 = p.constantCoeff := by
  change polynomialPairing p (MvPolynomial.monomial 0 1) = _
  rw [polynomialPairing_monomial_right]
  simp [exponentFactorial, MvPolynomial.constantCoeff_eq]

/-- Multiplication by the primitive image of a variable transposes to the
sum of partial derivatives in the two factors. -/
theorem polynomialTensorPairing_mul_primitive (i : Mode) (p q : Poly)
    (t : SymmetricCoefficients ⊗[ℂ] SymmetricCoefficients) :
    polynomialTensorPairing p q
      (t * ((show SymmetricCoefficients from MvPolynomial.X i) ⊗ₜ[ℂ] 1 +
        1 ⊗ₜ[ℂ] (show SymmetricCoefficients from MvPolynomial.X i))) =
      polynomialTensorPairing (MvPolynomial.pderiv i p) q t +
        polynomialTensorPairing p (MvPolynomial.pderiv i q) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu =>
    simp only [add_mul, map_add, ht, hu]
    abel
  | tmul r s =>
    simp only [mul_add, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
      map_add, polynomialTensorPairing_tmul, polynomialPairing_pderiv]
    rw [mul_comm r (MvPolynomial.X i), mul_comm s (MvPolynomial.X i)]

/-- No degree-dependent normalization is suppressed: the factorial pairing
is exactly dual to the existing primitive symmetric coproduct. -/
theorem polynomialPairing_mul_coproduct (p q r : Poly) :
    polynomialPairing (p*q) r =
      polynomialTensorPairing p q
        (symmetricCoproductAlg (show SymmetricCoefficients from r)) := by
  have h (r : Poly) : ∀ p q : Poly, polynomialPairing (p*q) r =
      polynomialTensorPairing p q
        (symmetricCoproductAlg (show SymmetricCoefficients from r)) := by
    induction r using MvPolynomial.induction_on with
    | C c =>
      intro p q
      have hc : (MvPolynomial.C c : Poly) = c • 1 := by
        change MvPolynomial.monomial 0 c = c • MvPolynomial.monomial 0 (1 : ℂ)
        rw [← map_smul, smul_eq_mul, mul_one]
      rw [hc]
      simp only [map_smul, map_one, Algebra.TensorProduct.one_def,
        polynomialTensorPairing_tmul, polynomialPairing_one_right, map_mul]
    | add r s hr hs =>
      intro p q
      simp only [map_add, hr, hs]
    | mul_X r i hr =>
      intro p q
      have hd : MvPolynomial.pderiv i (p*q) =
          MvPolynomial.pderiv i p * q + p * MvPolynomial.pderiv i q := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
        ring
      calc
        polynomialPairing (p*q) (r * MvPolynomial.X i) =
            polynomialPairing (MvPolynomial.pderiv i (p*q)) r := by
          rw [polynomialPairing_pderiv, mul_comm r (MvPolynomial.X i)]
        _ = polynomialPairing (MvPolynomial.pderiv i p * q) r +
            polynomialPairing (p * MvPolynomial.pderiv i q) r := by
          rw [hd, map_add, LinearMap.add_apply]
        _ = polynomialTensorPairing (MvPolynomial.pderiv i p) q (symmetricCoproductAlg r) +
            polynomialTensorPairing p (MvPolynomial.pderiv i q) (symmetricCoproductAlg r) := by
          rw [hr, hr]
        _ = polynomialTensorPairing p q (symmetricCoproductAlg (r * MvPolynomial.X i)) := by
          rw [map_mul, symmetricCoproductAlg_X, polynomialTensorPairing_mul_primitive]
  exact h r p q

end KhanSL2.Macdonald
