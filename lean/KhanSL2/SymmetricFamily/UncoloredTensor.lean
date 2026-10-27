module

public import KhanSL2.SymmetricFamily.UncoloredWords
public import KhanSL2.SymmetricFamily.SignedTensor
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.Algebra.Polynomial.Basis

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Actual tensors of one-variable polynomials as labelled-root polynomials. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG

/-- The actual monomial tensor basis, indexed by ordered exponent words. -/
def polynomialWordBasis (k : ℕ) :
    Module.Basis (Fin k → ℕ) ℂ (⨂[ℂ]^k (Polynomial ℂ)) :=
  Basis.piTensorProduct (fun _ : Fin k => Polynomial.basisMonomials ℂ)

@[simp] theorem polynomialWordBasis_apply (k : ℕ) (u : Fin k → ℕ) :
    polynomialWordBasis k u = PiTensorProduct.tprod ℂ (fun i => (Polynomial.X : Polynomial ℂ) ^ u i) := by
  simp only [polynomialWordBasis, Basis.piTensorProduct_apply,
    Polynomial.coe_basisMonomials, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_1, one_mul]

/-- Ordered polynomial tensor monomials become actual labelled-root monomials. -/
def polynomialTensorEquiv (k : ℕ) :
    (⨂[ℂ]^k (Polynomial ℂ)) ≃ₗ[ℂ] MvPolynomial (Fin k) ℂ :=
  (polynomialWordBasis k).repr.trans (wordPolynomialEquiv k)

@[simp] theorem polynomialTensorEquiv_basis (k : ℕ) (u : Fin k → ℕ) :
    polynomialTensorEquiv k (polynomialWordBasis k u) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm u) 1 := by
  simp only [polynomialTensorEquiv, LinearEquiv.trans_apply, Module.Basis.repr_self,
    wordPolynomialEquiv_single]

@[simp] theorem polynomialTensorEquiv_word (k : ℕ) (u : Fin k → ℕ) :
    polynomialTensorEquiv k (PiTensorProduct.tprod ℂ
      (fun i => (Polynomial.X : Polynomial ℂ) ^ u i)) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm u) 1 := by
  rw [← polynomialWordBasis_apply, polynomialTensorEquiv_basis]

theorem polynomialWordBasis_repr_permute {k : ℕ} (σ : Equiv.Perm (Fin k))
    (x : ⨂[ℂ]^k (Polynomial ℂ)) :
    (polynomialWordBasis k).repr (slotPermute (Polynomial ℂ) σ x) =
      wordPermute σ ((polynomialWordBasis k).repr x) := by
  have h : (polynomialWordBasis k).repr.toLinearMap.comp
      (slotPermute (Polynomial ℂ) σ).toLinearMap =
      (wordPermute σ).comp (polynomialWordBasis k).repr.toLinearMap := by
    apply (polynomialWordBasis k).ext
    intro u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      wordPermute_single]
    rw [polynomialWordBasis_apply, slotPermute_tprod]
    simpa only [polynomialWordBasis_apply, Function.comp_def] using
      Module.Basis.repr_self (polynomialWordBasis k) (u ∘ σ)
  exact LinearMap.congr_fun h x

/-- Actual slot permutation becomes the corresponding renaming of labelled roots. -/
theorem polynomialTensorEquiv_permute {k : ℕ} (σ : Equiv.Perm (Fin k))
    (x : ⨂[ℂ]^k (Polynomial ℂ)) :
    polynomialTensorEquiv k (slotPermute (Polynomial ℂ) σ x) =
      MvPolynomial.rename σ.symm (polynomialTensorEquiv k x) := by
  change wordPolynomialEquiv k ((polynomialWordBasis k).repr
    (slotPermute (Polynomial ℂ) σ x)) = _
  rw [polynomialWordBasis_repr_permute, wordPolynomialEquiv_permute]
  rfl

private theorem polynomialTensor_shift_word (m k : ℕ) (u : Fin k → ℕ) :
    polynomialTensorEquiv k (tensorDeriv k
      (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m))
      (PiTensorProduct.tprod ℂ (fun i => (Polynomial.X : Polynomial ℂ)^u i))) =
      MvPolynomial.psum (Fin k) ℂ m *
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm u) 1 := by
  rw [tensorDeriv_tprod, map_sum]
  have h (i : Fin k) : Function.update (fun j => (Polynomial.X : Polynomial ℂ)^u j) i
      (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)
        ((Polynomial.X : Polynomial ℂ)^u i)) =
      (fun j => (Polynomial.X : Polynomial ℂ)^(Function.update u i (u i+m) j)) := by
    funext j
    by_cases hj : j=i
    · subst j; simp [LinearMap.mulLeft_apply, pow_add, mul_comm]
    · simp [hj, Function.update_of_ne hj]
  simp only [h, polynomialTensorEquiv_word, MvPolynomial.psum, Finset.sum_mul,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, one_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hd : Finsupp.equivFunOnFinite.symm (Function.update u i (u i+m)) =
      Finsupp.single i m + Finsupp.equivFunOnFinite.symm u := by
    ext j
    by_cases hj : j=i
    · subst j; simp [Nat.add_comm]
    · simp [hj, Ne.symm hj, Function.update_of_ne hj]
  exact congrArg (fun d => MvPolynomial.monomial d (1:ℂ)) hd

/-- The original multiplication-by-X^m derivation is multiplication by the root power sum. -/
theorem polynomialTensorEquiv_shift (m k : ℕ) (x : ⨂[ℂ]^k (Polynomial ℂ)) :
    polynomialTensorEquiv k (tensorDeriv k
      (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) x) =
      MvPolynomial.psum (Fin k) ℂ m * polynomialTensorEquiv k x := by
  have h : (polynomialTensorEquiv k).toLinearMap.comp
      (tensorDeriv k (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m))) =
      (LinearMap.mulLeft ℂ (MvPolynomial.psum (Fin k) ℂ m)).comp
        (polynomialTensorEquiv k).toLinearMap := by
    apply (polynomialWordBasis k).ext
    intro u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, polynomialTensorEquiv_basis,
      LinearMap.mulLeft_apply, polynomialWordBasis_apply, polynomialTensorEquiv_word]
    exact polynomialTensor_shift_word m k u
  exact LinearMap.congr_fun h x

end KhanSL2.SymmetricFamily
