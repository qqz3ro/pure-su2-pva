module

public import KhanSL2.Injectivity.CartanJets
public import KhanSL2.Injectivity.CartanSeriesWord
public import KhanSL2.Injectivity.TaylorCoefficients

/-! The Taylor coefficients of the actual canonical morphism are normalized
finite Cartan word pairings, with the exact Y-representative scalar. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace KhanSL2.Injectivity

theorem wordFactorial_ofFn {n : ℕ} (a : Fin n → ℕ) :
    Cartan.wordFactorial (List.ofFn a) = ∏ i, (Nat.factorial (a i) : ℂ) := by
  simp [Cartan.wordFactorial, List.map_ofFn, List.prod_ofFn]

theorem exponentFactorial_eq_wordFactorials {r s : ℕ}
    (d : SourceDual.Variables r s →₀ ℕ) :
    SourceDual.exponentFactorial d =
      Cartan.wordFactorial (List.ofFn fun i => d (.inl i)) *
        Cartan.wordFactorial (List.ofFn fun i => d (.inr i)) := by
  rw [wordFactorial_ofFn, wordFactorial_ofFn]
  exact Fintype.prod_sum_type _

theorem coeff_taylor_descended (r s N : ℕ)
    (f : Cartan.Cochain →ₗ[ℂ] ℂ) (hf : ∀ u, f (Cartan.q u) = 0)
    (d : SourceDual.Variables r s →₀ ℕ) :
    (SourceDual.taylorPolynomial r s N ((descendCartanFunctional f hf).comp phi)).coeff d =
      if d.degree = N then (-2 : ℂ) ^ s * f (Cartan.normalizedWord
        (List.ofFn fun i => d (.inl i)) (List.ofFn fun i => d (.inr i))) else 0 := by
  rw [SourceDual.coeff_taylorPolynomial_all]
  by_cases hd : d.degree = N
  · rw [if_pos hd, if_pos hd]
    change descendCartanFunctional f hf (phi (Source.jetMonomial _ _)) / _ = _
    rw [descendCartanFunctional_phi_jetMonomial, List.length_ofFn,
      exponentFactorial_eq_wordFactorials, mul_div_assoc, Cartan.normalizedWord_pairing]
  · rw [if_neg hd, if_neg hd]

/-- The actual canonical map's Taylor polynomial is the homogeneous part of
the explicit chain determinant, with the Y-generator normalization. -/
theorem taylor_descended_chainPolynomial (r s N : ℕ) (c : Cartan.Cochain)
    (hc : ∀ u, FiniteExterior.coefficientPairing c (Cartan.q u) = 0) :
    SourceDual.taylorPolynomial r s N
        ((descendCartanFunctional (FiniteExterior.coefficientPairing c) hc).comp phi) =
      (-2 : ℂ) ^ s • MvPolynomial.homogeneousComponent N (Cartan.chainPolynomial r s c) := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_taylor_descended, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_homogeneousComponent, Cartan.coeff_chainPolynomial]
  by_cases h : d.degree = N <;> simp [h, smul_eq_mul]

end KhanSL2.Injectivity
