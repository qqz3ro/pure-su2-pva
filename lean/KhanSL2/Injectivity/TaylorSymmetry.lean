module

public import KhanSL2.Injectivity.TaylorPolynomial
public import KhanSL2.Injectivity.MonomialSymmetry
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! The Taylor polynomial is symmetric in X variables and alternating in Y variables. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.SourceDual

open Source

theorem indexWeight_comp {r s N : ℕ} (a : TaylorIndex r s N)
    (e : Equiv.Perm (Variables r s)) : indexWeight (a ∘ e) = indexWeight a := by
  simp only [indexWeight_eq_sum, Function.comp_apply]
  exact Equiv.sum_comp e (fun i => (a i).val)

theorem jetFactorial_comp {r s N : ℕ} (a : TaylorIndex r s N)
    (e : Equiv.Perm (Variables r s)) : jetFactorial (a ∘ e) = jetFactorial a := by
  exact Equiv.prod_comp e (fun i => (Nat.factorial (a i).val : ℂ))

def indexEquiv {r s N : ℕ} (e : Equiv.Perm (Variables r s)) :
    Equiv.Perm (TaylorIndex r s N) where
  toFun a := a ∘ e
  invFun a := a ∘ e.symm
  left_inv a := by funext i; simp
  right_inv a := by funext i; simp

theorem mapDomain_exponent_comp {r s N : ℕ} (a : TaylorIndex r s N)
    (e : Equiv.Perm (Variables r s)) :
    Finsupp.mapDomain e (exponent (a ∘ e)) = exponent a := by
  ext i
  simp [Finsupp.mapDomain_equiv_apply, Function.comp_def]

/-- A permutation law on source monomials induces the corresponding polynomial law. -/
theorem rename_taylorPolynomial {r s N : ℕ} (ell : Source →ₗ[ℂ] ℂ)
    (e : Equiv.Perm (Variables r s)) (c : ℂ)
    (h : ∀ a : TaylorIndex r s N,
      ell (jetMonomial (xIndices (a ∘ e)) (yIndices (a ∘ e))) =
        c * ell (jetMonomial (xIndices a) (yIndices a))) :
    MvPolynomial.rename e (taylorPolynomial r s N ell) = c • taylorPolynomial r s N ell := by
  classical
  simp only [taylorPolynomial, map_sum, Finset.smul_sum]
  rw [← Equiv.sum_comp (indexEquiv (N := N) e)]
  refine Finset.sum_congr rfl fun a _ => ?_
  change MvPolynomial.rename e
    (if indexWeight (a ∘ e) = N then
      MvPolynomial.monomial (exponent (a ∘ e))
        (ell (jetMonomial (xIndices (a ∘ e)) (yIndices (a ∘ e))) / jetFactorial (a ∘ e))
    else 0) = _
  rw [indexWeight_comp]
  by_cases ha : indexWeight a = N
  · simp only [ha, if_pos, MvPolynomial.rename_monomial, mapDomain_exponent_comp,
      jetFactorial_comp, h, MvPolynomial.smul_monomial, smul_eq_mul]
    rw [mul_div_assoc]
  · simp [ha]

def xPermutation {r s : ℕ} (σ : Equiv.Perm (Fin r)) : Equiv.Perm (Variables r s) :=
  Equiv.sumCongr σ (Equiv.refl _)

def yPermutation {r s : ℕ} (σ : Equiv.Perm (Fin s)) : Equiv.Perm (Variables r s) :=
  Equiv.sumCongr (Equiv.refl _) σ

theorem jetMonomial_comp_xPermutation {r s N : ℕ} (a : TaylorIndex r s N)
    (σ : Equiv.Perm (Fin r)) :
    jetMonomial (xIndices (a ∘ xPermutation σ)) (yIndices (a ∘ xPermutation σ)) =
      jetMonomial (xIndices a) (yIndices a) := by
  change xProduct (List.ofFn ((fun i => (a (Sum.inl i)).val) ∘ σ)) *
      yProduct (yIndices a) = _
  rw [xProduct_ofFn_comp_perm]
  rfl

theorem jetMonomial_comp_yPermutation {r s N : ℕ} (a : TaylorIndex r s N)
    (σ : Equiv.Perm (Fin s)) :
    jetMonomial (xIndices (a ∘ yPermutation σ)) (yIndices (a ∘ yPermutation σ)) =
      Equiv.Perm.sign σ • jetMonomial (xIndices a) (yIndices a) := by
  change xProduct (xIndices a) *
      yProduct (List.ofFn ((fun i => (a (Sum.inr i)).val) ∘ σ)) = _
  rw [yProduct_ofFn_comp_perm]
  change xProduct (xIndices a) * (Equiv.Perm.sign σ • yProduct (yIndices a)) =
    Equiv.Perm.sign σ • (xProduct (xIndices a) * yProduct (yIndices a))
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, mul_smul_comm]

theorem taylorPolynomial_symmetric_x {r s N : ℕ} (ell : Source →ₗ[ℂ] ℂ)
    (σ : Equiv.Perm (Fin r)) :
    MvPolynomial.rename (xPermutation σ) (taylorPolynomial r s N ell) =
      taylorPolynomial r s N ell := by
  simpa only [one_smul] using rename_taylorPolynomial ell (xPermutation σ) 1
    (fun a => by rw [jetMonomial_comp_xPermutation]; simp)

theorem taylorPolynomial_alternating_y {r s N : ℕ} (ell : Source →ₗ[ℂ] ℂ)
    (σ : Equiv.Perm (Fin s)) :
    MvPolynomial.rename (yPermutation σ) (taylorPolynomial r s N ell) =
      (((Equiv.Perm.sign σ : ℤ) : ℂ)) • taylorPolynomial r s N ell := by
  apply rename_taylorPolynomial
  intro a
  rw [jetMonomial_comp_yPermutation]
  simp only [Units.smul_def, ← Int.cast_smul_eq_zsmul ℂ, map_smul, smul_eq_mul]

end KhanSL2.SourceDual
