module

public import KhanSL2.SymmetricFamily.WordBlock
public import KhanSL2.SymmetricFamily.UncoloredWords
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Literal restriction of labelled root polynomials to two alphabets, with
its exact ordered-word formula. This is the restriction used by the chart maps. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily

/-- Send the first r root variables to the first tensor factor and the last t
to the second; no averaging or scalar normalization occurs in this map. -/
def rootPolynomialBlock (r t : ℕ) : MvPolynomial (Fin (r+t)) ℂ →ₐ[ℂ]
    MvPolynomial (Fin r) ℂ ⊗[ℂ] MvPolynomial (Fin t) ℂ :=
  MvPolynomial.aeval (Fin.addCases
    (fun i : Fin r => (MvPolynomial.X i : MvPolynomial (Fin r) ℂ) ⊗ₜ[ℂ] 1)
    (fun j : Fin t => 1 ⊗ₜ[ℂ] (MvPolynomial.X j : MvPolynomial (Fin t) ℂ)))

@[simp] theorem rootPolynomialBlock_X_left (r t : ℕ) (i : Fin r) :
    rootPolynomialBlock r t (MvPolynomial.X (Fin.castAdd t i)) =
      (MvPolynomial.X i : MvPolynomial (Fin r) ℂ) ⊗ₜ[ℂ] (1 : MvPolynomial (Fin t) ℂ) := by
  simp [rootPolynomialBlock]

@[simp] theorem rootPolynomialBlock_X_right (r t : ℕ) (j : Fin t) :
    rootPolynomialBlock r t (MvPolynomial.X (Fin.natAdd r j)) =
      (1 : MvPolynomial (Fin r) ℂ) ⊗ₜ[ℂ] (MvPolynomial.X j : MvPolynomial (Fin t) ℂ) := by
  simp [rootPolynomialBlock]

theorem wordPolynomialEquiv_single_one_product (k : ℕ) (u : Fin k → ℕ) :
    wordPolynomialEquiv k (Finsupp.single u 1) =
      ∏ i : Fin k, (MvPolynomial.X i : MvPolynomial (Fin k) ℂ)^u i := by
  rw [wordPolynomialEquiv_single,MvPolynomial.monomial_eq,MvPolynomial.C_1,one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

/-- The literal root restriction agrees with restriction of ordered exponent words. -/
theorem rootPolynomialBlock_word (r t : ℕ) (x : WordSpace ℕ (r+t)) :
    rootPolynomialBlock r t (wordPolynomialEquiv (r+t) x) =
      TensorProduct.map (wordPolynomialEquiv r).toLinearMap
        (wordPolynomialEquiv t).toLinearMap (wordBlock r t x) := by
  have h1 (u : Fin (r+t) → ℕ) :
      rootPolynomialBlock r t (wordPolynomialEquiv (r+t) (Finsupp.single u 1)) =
        wordPolynomialEquiv r (Finsupp.single (u ∘ Fin.castAdd t) 1) ⊗ₜ[ℂ]
          wordPolynomialEquiv t (Finsupp.single (u ∘ Fin.natAdd r) 1) := by
    rw [wordPolynomialEquiv_single_one_product,map_prod,Fin.prod_univ_add]
    simp only [map_pow,rootPolynomialBlock_X_left,rootPolynomialBlock_X_right,
      Algebra.TensorProduct.tmul_pow,one_pow]
    change (∏ i : Fin r, ((Algebra.TensorProduct.includeLeft : MvPolynomial (Fin r) ℂ →ₐ[ℂ]
      MvPolynomial (Fin r) ℂ ⊗[ℂ] MvPolynomial (Fin t) ℂ)
      ((MvPolynomial.X i : MvPolynomial (Fin r) ℂ)^u (Fin.castAdd t i)))) *
      (∏ i : Fin t, ((Algebra.TensorProduct.includeRight : MvPolynomial (Fin t) ℂ →ₐ[ℂ]
        MvPolynomial (Fin r) ℂ ⊗[ℂ] MvPolynomial (Fin t) ℂ)
        ((MvPolynomial.X i : MvPolynomial (Fin t) ℂ)^u (Fin.natAdd r i)))) = _
    rw [← map_prod,← map_prod]
    simp only [Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul,
      wordPolynomialEquiv_single_one_product,Function.comp_apply]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | single u c =>
    have hc : Finsupp.single u c = c • Finsupp.single u (1:ℂ) := by simp
    rw [hc,map_smul,map_smul,map_smul,map_smul,wordBlock_single,one_smul,TensorProduct.map_tmul]
    exact congrArg (fun z => c • z) (h1 u)

end KhanSL2.SymmetricFamily
