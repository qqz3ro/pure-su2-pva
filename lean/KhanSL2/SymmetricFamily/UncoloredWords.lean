module

public import KhanSL2.SymmetricFamily.WordInvariants
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

@[expose] public section

/-! One-color symmetric root polynomials from normalized invariant words.
This reusable comparison is independent of current colors or root multiplicity. -/

noncomputable section
namespace KhanSL2.SymmetricFamily

/-- A labelled word of polynomial exponents is the corresponding root monomial. -/
def wordPolynomialEquiv (k : ℕ) : WordSpace ℕ k ≃ₗ[ℂ] MvPolynomial (Fin k) ℂ :=
  (Finsupp.domLCongr Finsupp.equivFunOnFinite.symm).trans
    (MvPolynomial.basisMonomials (Fin k) ℂ).repr.symm

@[simp] theorem wordPolynomialEquiv_single (k : ℕ) (u : Fin k → ℕ) (c : ℂ) :
    wordPolynomialEquiv k (Finsupp.single u c) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm u) c := by
  simp only [wordPolynomialEquiv, LinearEquiv.trans_apply, Finsupp.domLCongr_single,
    Module.Basis.repr_symm_single, MvPolynomial.coe_basisMonomials,
    MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

/-- Actual word permutation becomes renaming of the labelled root variables. -/
theorem wordPolynomialEquiv_permute {k : ℕ} (σ : Equiv.Perm (Fin k)) (x : WordSpace ℕ k) :
    wordPolynomialEquiv k (wordPermute σ x) = MvPolynomial.rename σ.symm (wordPolynomialEquiv k x) := by
  have h : (wordPolynomialEquiv k).toLinearMap.comp (wordPermute σ) =
      (MvPolynomial.rename σ.symm).toLinearMap.comp (wordPolynomialEquiv k).toLinearMap := by
    apply Finsupp.lhom_ext
    intro u c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, wordPermute_single,
      wordPolynomialEquiv_single, AlgHom.toLinearMap_apply, MvPolynomial.rename_monomial]
    have hd : Finsupp.equivFunOnFinite.symm (u ∘ σ) =
        Finsupp.mapDomain σ.symm (Finsupp.equivFunOnFinite.symm u) := by
      ext i
      simp [Function.comp_def, Finsupp.mapDomain_equiv_apply]
    exact congrArg (fun d => MvPolynomial.monomial d c) hd
  exact LinearMap.congr_fun h x

/-- Invariant one-color words are precisely actual symmetric root polynomials. -/
def invariantWordPolynomialEquiv (k : ℕ) :
    invariantWords (α := ℕ) k ≃ₗ[ℂ] MvPolynomial.symmetricSubalgebra (Fin k) ℂ where
  toFun x := ⟨wordPolynomialEquiv k x.val, by
    intro σ
    have h := wordPolynomialEquiv_permute σ.symm x.val
    rw [Equiv.symm_symm, x.property σ.symm] at h
    exact h.symm⟩
  invFun x := ⟨(wordPolynomialEquiv k).symm x.val, by
    intro σ
    apply (wordPolynomialEquiv k).injective
    rw [wordPolynomialEquiv_permute, LinearEquiv.apply_symm_apply]
    exact x.property σ.symm⟩
  left_inv x := by
    apply Subtype.ext
    exact (wordPolynomialEquiv k).symm_apply_apply x.val
  right_inv x := by
    apply Subtype.ext
    exact (wordPolynomialEquiv k).apply_symm_apply x.val
  map_add' x y := by apply Subtype.ext; exact map_add (wordPolynomialEquiv k) x.val y.val
  map_smul' c x := by apply Subtype.ext; exact map_smul (wordPolynomialEquiv k) c x.val

/-- Normalized symmetric-power monomial coordinates identify with the symmetric root ring. -/
def exponentSymmetricPolynomialEquiv (k : ℕ) :
    ExponentSpace ℕ k ≃ₗ[ℂ] MvPolynomial.symmetricSubalgebra (Fin k) ℂ :=
  (exponentInvariantEquiv k).trans (invariantWordPolynomialEquiv k)

end KhanSL2.SymmetricFamily
