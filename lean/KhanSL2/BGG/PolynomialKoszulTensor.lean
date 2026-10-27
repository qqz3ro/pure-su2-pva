module

public import KhanSL2.BGG.PolynomialKoszulFinite

@[expose] public section

/-! Pure-tensor formulas for the actual polynomial Koszul operators. -/
noncomputable section
open scoped BigOperators TensorProduct
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PolynomialKoszul

theorem d_tmul_monomial (p : Poly) (t : Finset Mode) :
    d (p ⊗ₜ[ℂ] monomial t) =
      ∑ i∈t, (MvPolynomial.X i * p) ⊗ₜ[ℂ] PositiveCE.contract i (monomial t) := by
  let φ : Poly →ₗ[ℂ] Chain := (TensorProduct.mk ℂ Poly Exterior).flip (monomial t)
  have heq : d.comp φ = (finiteD t).comp φ := by
    apply (MvPolynomial.basisMonomials Mode ℂ).ext
    intro s
    change d (MvPolynomial.monomial s 1 ⊗ₜ[ℂ] monomial t) =
      finiteD t (MvPolynomial.monomial s 1 ⊗ₜ[ℂ] monomial t)
    rw [← basis_apply, finiteD_basis_eq t (s,t) (Finset.Subset.refl t)]
  have h := LinearMap.congr_fun heq p
  change d (p ⊗ₜ[ℂ] monomial t) = finiteD t (p ⊗ₜ[ℂ] monomial t) at h
  simpa only [finiteD_apply, dTerm_tmul] using h

theorem H_monomial_tmul (s : Exponent) (u : Exterior) :
    H (MvPolynomial.monomial s 1 ⊗ₜ[ℂ] u) =
      ∑ i∈s.support, MvPolynomial.pderiv i (MvPolynomial.monomial s 1) ⊗ₜ[ℂ]
        (FiniteExterior.generator i * u) := by
  let φ : Exterior →ₗ[ℂ] Chain := TensorProduct.mk ℂ Poly Exterior (MvPolynomial.monomial s 1)
  have heq : H.comp φ = (finiteH s.support).comp φ := by
    apply (Finsupp.basisSingleOne : Module.Basis (Finset Mode) ℂ Exterior).ext
    intro t
    change H (MvPolynomial.monomial s 1 ⊗ₜ[ℂ] monomial t) =
      finiteH s.support (MvPolynomial.monomial s 1 ⊗ₜ[ℂ] monomial t)
    rw [← basis_apply, finiteH_basis_eq s.support (s,t) (Finset.Subset.refl s.support)]
  have h := LinearMap.congr_fun heq u
  change H (MvPolynomial.monomial s 1 ⊗ₜ[ℂ] u) =
    finiteH s.support (MvPolynomial.monomial s 1 ⊗ₜ[ℂ] u) at h
  simpa only [finiteH_apply, hTerm_tmul] using h

end KhanSL2.BGG.PolynomialKoszul
