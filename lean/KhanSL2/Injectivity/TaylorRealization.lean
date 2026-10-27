module

public import KhanSL2.Injectivity.SourcePolynomialSpan
public import KhanSL2.Injectivity.TaylorLinear

@[expose] public section

/-! Linear assembly of the explicit cycle-polynomial realizations. -/

noncomputable section
open scoped BigOperators

namespace KhanSL2.SourceDual

open Injectivity MvPolynomial

variable {H : Type*} [AddCommGroup H] [Module ℂ H]

/-- Linear assembly needs the pairing only for the explicit spanning family.
The homogeneous projection handles arbitrary degrees of the chosen chains. -/
theorem taylor_realization_of_cycle_polynomials (r s N : ℕ) (f : Source →ₗ[ℂ] H)
    (realize : ∀ (e : Fin r → ℕ) (q : MvPolynomial (Fin s) ℂ), q.IsSymmetric →
      ∃ ellH : H →ₗ[ℂ] ℂ,
        taylorPolynomial r s N (ellH.comp f) = homogeneousComponent N (cyclePolynomial r s e q))
    (ell : Source →ₗ[ℂ] ℂ) :
    ∃ ellH : H →ₗ[ℂ] ℂ,
      taylorPolynomial r s N (ellH.comp f) = taylorPolynomial r s N ell := by
  have hspan := taylorPolynomial_mem_cyclePolynomialSpan r s N ell
  have h : ∀ p ∈ cyclePolynomialSpan r s, ∃ ellH : H →ₗ[ℂ] ℂ,
      taylorPolynomial r s N (ellH.comp f) = homogeneousComponent N p := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨⟨e, ⟨q, hq⟩⟩, rfl⟩ := hp
      exact realize e q hq
    | zero =>
      refine ⟨0, ?_⟩
      change taylorPolynomialLinear r s N ((0 : H →ₗ[ℂ] ℂ).comp f) = _
      simp
    | add p q _ _ hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      refine ⟨a + b, ?_⟩
      change taylorPolynomialLinear r s N ((a + b).comp f) = _
      rw [LinearMap.add_comp, map_add, taylorPolynomialLinear_apply,
        taylorPolynomialLinear_apply, ha, hb, map_add]
    | smul c p _ hp =>
      obtain ⟨a, ha⟩ := hp
      refine ⟨c • a, ?_⟩
      change taylorPolynomialLinear r s N ((c • a).comp f) = _
      rw [LinearMap.smul_comp, map_smul, taylorPolynomialLinear_apply, ha, map_smul]
  obtain ⟨ellH, hH⟩ := h _ hspan
  refine ⟨ellH, hH.trans ?_⟩
  exact homogeneousComponent_eq_self (taylorPolynomial_homogeneous r s N ell)

/-- Explicit determinant normalizations may be arbitrary nonzero scalars;
rescaling the actual target functional removes them. -/
theorem taylor_realization_of_nonzero_cycle_multiples (r s N : ℕ) (f : Source →ₗ[ℂ] H)
    (realize : ∀ (e : Fin r → ℕ) (q : MvPolynomial (Fin s) ℂ), q.IsSymmetric →
      ∃ (ellH : H →ₗ[ℂ] ℂ) (c : ℂ), c ≠ 0 ∧
        taylorPolynomial r s N (ellH.comp f) = c • homogeneousComponent N (cyclePolynomial r s e q))
    (ell : Source →ₗ[ℂ] ℂ) :
    ∃ ellH : H →ₗ[ℂ] ℂ,
      taylorPolynomial r s N (ellH.comp f) = taylorPolynomial r s N ell := by
  apply taylor_realization_of_cycle_polynomials r s N f ?_ ell
  intro e q hq
  obtain ⟨ellH, c, hc, h⟩ := realize e q hq
  refine ⟨c⁻¹ • ellH, ?_⟩
  change taylorPolynomialLinear r s N ((c⁻¹ • ellH).comp f) = _
  rw [LinearMap.smul_comp, map_smul, taylorPolynomialLinear_apply, h,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

end KhanSL2.SourceDual
