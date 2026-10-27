module

public import KhanSL2.SymmetricFamily.TensorMultiplication
public import KhanSL2.Macdonald.SymmetricCoefficientsComponents

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The actual symmetric coproduct is a sum over subsets of labelled slots.
This records the combinatorics needed to compare it with chart factorization. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open Macdonald

/-- The product associated to any chosen subset of a current word. -/
def subsetWord {k : ℕ} (v : Fin k → BGG.Current) (S : Finset (Fin k)) : SymmetricCoefficients :=
  ∏ i ∈ S, currentVariable (v i)

/-- Each subset product has precisely its subset's symmetric degree. -/
theorem subsetWord_mem_degree {k : ℕ} (v : Fin k → BGG.Current) (S : Finset (Fin k)) :
    subsetWord v S ∈ symmetricPower S.card := by
  change (∏ i ∈ S, currentVariable (v i) : Poly).IsHomogeneous S.card
  simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
    (MvPolynomial.IsHomogeneous.prod S (fun i => currentVariable (v i)) (fun _ => 1)
      (fun i _ => currentVariable_mem_degree_one (v i)))

private theorem prod_tmul_left {k : ℕ} (v : Fin k → BGG.Current) (S : Finset (Fin k)) :
    (∏ i ∈ S, (show SymmetricCoefficients from currentVariable (v i)) ⊗ₜ[ℂ] (1 : SymmetricCoefficients)) =
      subsetWord v S ⊗ₜ[ℂ] (1 : SymmetricCoefficients) := by
  induction S using Finset.induction_on with
  | empty => simp [subsetWord, Algebra.TensorProduct.one_def]
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi, subsetWord, ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private theorem prod_tmul_right {k : ℕ} (v : Fin k → BGG.Current) (S : Finset (Fin k)) :
    (∏ i ∈ S, (1 : SymmetricCoefficients) ⊗ₜ[ℂ] (show SymmetricCoefficients from currentVariable (v i))) =
      (1 : SymmetricCoefficients) ⊗ₜ[ℂ] subsetWord v S := by
  induction S using Finset.induction_on with
  | empty => simp [subsetWord, Algebra.TensorProduct.one_def]
  | @insert i S hi ih =>
    simp only [Finset.prod_insert hi, subsetWord, ih, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- Exact labelled-slot formula for the already defined primitive coproduct. -/
theorem symmetricCoproduct_word (k : ℕ) (v : Fin k → BGG.Current) :
    symmetricCoproductAlg (subsetWord v Finset.univ) =
      ∑ S : Finset (Fin k), subsetWord v S ⊗ₜ[ℂ] subsetWord v Sᶜ := by
  rw [subsetWord, map_prod]
  simp only [symmetricCoproduct_currentVariable]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [prod_tmul_left, prod_tmul_right, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- The same formula on the actual homogeneous multiplication quotient. -/
theorem symmetricCoproduct_tensorToSymmetric (k : ℕ) (v : Fin k → BGG.Current) :
    symmetricCoproductAlg (tensorToSymmetric k (PiTensorProduct.tprod ℂ v)) =
      ∑ S : Finset (Fin k), subsetWord v S ⊗ₜ[ℂ] subsetWord v Sᶜ := by
  have h : (tensorToSymmetric k (PiTensorProduct.tprod ℂ v) : SymmetricCoefficients) =
      subsetWord v Finset.univ := tensorToSymmetric_tprod k v
  rw [h]
  exact symmetricCoproduct_word k v

end KhanSL2.SymmetricFamily
