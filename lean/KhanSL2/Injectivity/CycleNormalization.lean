module

public import KhanSL2.Injectivity.CartanBlockDeterminant
public import KhanSL2.Injectivity.CyclePolynomialIdentities

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity.Cartan

open MvPolynomial

/-- Exact nonzero scalar from the source slot order, the Newton rows, and
the two root antisymmetrizations. -/
def selectedCycleScalar (r s : ℕ) : ℂ :=
  (sourceOrderingSign r s : ℂ) * (-1 : ℂ) ^ (r * s + r) * (s.factorial : ℂ) ^ 2

theorem selectedCycleScalar_ne_zero (r s : ℕ) : selectedCycleScalar r s ≠ 0 := by
  have hs : (sourceOrderingSign r s : ℂ) ≠ 0 := by
    rcases Int.units_eq_one_or (sourceOrderingSign r s) with h | h <;> simp [h]
  have hf : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
  exact mul_ne_zero (mul_ne_zero hs (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))) (pow_ne_zero _ hf)

theorem selectedCycleNormalization (r s : ℕ) (e : Fin r → ℕ)
    (p : MvPolynomial (Fin s) ℂ) :
    (sourceOrderingSign r s : EvaluationPolynomial r s) *
      (((-1 : EvaluationPolynomial r s) ^ (r * s) *
        xVandermonde r s * yVandermonde r s * crossFactor r s) *
        (((-1 : EvaluationPolynomial r s) ^ r * crossFactor r s *
          rename Sum.inl (TauCeti.alternant (Fin r) ℂ e)) *
          ((s.factorial : EvaluationPolynomial r s) ^ 2 *
            (yVandermonde r s ^ 2 * rename Sum.inr p)))) =
      selectedCycleScalar r s • cyclePolynomial r s e p := by
  simp only [selectedCycleScalar, cyclePolynomial, Algebra.smul_def, map_mul, map_pow,
    map_intCast, map_neg, map_one, map_natCast, pow_add]
  ring

end KhanSL2.Injectivity.Cartan
