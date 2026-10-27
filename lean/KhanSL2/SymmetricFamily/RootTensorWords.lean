module

public import KhanSL2.SymmetricFamily.FactorInsertion
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The original labelled-current basis after coefficient specialization, and
literal root restriction to the two distinguished blocks. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald
open scoped FactorRootScalars

/-- Ordered root monomials are the literal product of their root variables. -/
theorem rootMonomial_eq_product (k : ℕ) (a : Fin k → ℕ) :
    (show RootPolynomial k from MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) 1) =
      ∏ i : Fin k, (show RootPolynomial k from MvPolynomial.X i)^a i := by
  change (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) 1 : MvPolynomial (Fin k) ℂ) = _
  rw [MvPolynomial.monomial_eq,MvPolynomial.C_1,one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

/-- Actual scalar extension of a basis tensor evaluates its monomial at the original roots. -/
theorem baseRootTensorEquiv_word_unit (k : ℕ) (A : Type) [CommRing A]
    [Algebra (Depth.RB k) A] [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB k) A]
    (a : Fin k → ℕ) (v : Fin k → Fin 3) :
    baseRootTensorEquiv k A
      (1 ⊗ₜ[Depth.RB k] PiTensorProduct.tprod ℂ (fun i => BGG.currentBasis (a i,v i))) =
        (∏ i, baseRoot k A i ^ a i) ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin k → Fin 3) v := by
  rw [baseRootTensorEquiv_tmul,rootTensorEquiv_word,
    TensorProduct.AlgebraTensorModule.assoc_symm_tmul]
  change rootBaseRight k A
    (show RootPolynomial k from MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm a) 1)
      ⊗ₜ[ℂ] _ = _
  rw [rootMonomial_eq_product,map_prod]
  simp only [map_pow,baseRoot]

/-- The same basis formula for a prescribed factor coefficient algebra. -/
theorem factorTensorUnit_word {A : Type} [CommRing A] [Algebra ℂ A]
    (k : ℕ) (f : Polynomial A) (a : Fin k → ℕ) (v : Fin k → Fin 3) :
    factorTensorUnit k f (PiTensorProduct.tprod ℂ (fun i => BGG.currentBasis (a i,v i))) =
      (∏ i, factorRoot k f i ^ a i) ⊗ₜ[ℂ] Pi.basisFun ℂ (Fin k → Fin 3) v := by
  let := factorCoefficientAlgebra k f
  let : IsScalarTower ℂ (Depth.RB k) A :=
    IsScalarTower.of_algebraMap_eq fun z => ((Collision.coeffHom k f).commutes z).symm
  exact baseRootTensorEquiv_word_unit k A a v

variable {r s : ℕ} {A : Type} [CommRing A] [Algebra (Depth.RB (r+s)) A]
  [Algebra ℂ A] [IsScalarTower ℂ (Depth.RB (r+s)) A]

omit [IsScalarTower ℂ (Depth.RB (r+s)) A] in
/-- The actual first-block quotient sends each root monomial to its two factor monomials. -/
theorem blockFactorTensorEquiv_root_product (c : Collision.ChartData (r+s) r s A)
    (a : Fin (r+s) → ℕ) :
    blockFactorTensorEquiv c (Ideal.Quotient.mk _ (∏ i, baseRoot (r+s) A i ^ a i)) =
      (∏ i : Fin r, factorRoot r c.f₁ i ^ a (Fin.castAdd s i)) ⊗ₜ[A]
        (∏ i : Fin s, factorRoot s c.f₂ i ^ a (Fin.natAdd r i)) := by
  change blockFactorToTensor c ((Ideal.Quotient.mkₐ A _) (∏ i, baseRoot (r+s) A i ^ a i)) = _
  simp only [map_prod,map_pow]
  change (∏ i : Fin (r+s), blockFactorToTensor c (blockRoot c i)^a i) = _
  rw [Fin.prod_univ_add]
  simp only [blockFactorToTensor_leftRoot,blockFactorToTensor_rightRoot,
    blockTensorLeftRoot,blockTensorRightRoot,Algebra.TensorProduct.tmul_pow,one_pow]
  change (∏ i : Fin r, (Algebra.TensorProduct.includeLeft : FactorRoots r c.f₁ →ₐ[A]
    BlockRootTensor c) (factorRoot r c.f₁ i ^ a (Fin.castAdd s i))) *
    (∏ i : Fin s, (Algebra.TensorProduct.includeRight : FactorRoots s c.f₂ →ₐ[A]
      BlockRootTensor c) (factorRoot s c.f₂ i ^ a (Fin.natAdd r i))) = _
  rw [← map_prod,← map_prod]
  simp only [Algebra.TensorProduct.includeLeft_apply,Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

/-- Exact colored root restriction on every original basis tensor. -/
theorem coloredBlockTensorEquiv_word (c : Collision.ChartData (r+s) r s A)
    (a : Fin (r+s) → ℕ) (v : Fin (r+s) → Fin 3) :
    coloredBlockTensorEquiv c
      (coloredAssignmentSplitting (r+s) A c
        (baseRootTensorEquiv (r+s) A
          (1 ⊗ₜ[Depth.RB (r+s)] PiTensorProduct.tprod ℂ (fun i => BGG.currentBasis (a i,v i))))
        (firstBlock r s)) =
      factorTensorUnit r c.f₁ (PiTensorProduct.tprod ℂ (fun i => BGG.currentBasis (a (Fin.castAdd s i),v (Fin.castAdd s i)))) ⊗ₜ[A]
        factorTensorUnit s c.f₂ (PiTensorProduct.tprod ℂ (fun i => BGG.currentBasis (a (Fin.natAdd r i),v (Fin.natAdd r i)))) := by
  rw [baseRootTensorEquiv_word_unit,coloredAssignmentSplitting_tmul,
    factorTensorUnit_word,factorTensorUnit_word]
  simp only [coloredBlockTensorEquiv,LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.congr_tmul,AlgEquiv.coe_toLinearEquiv,
    blockFactorTensorEquiv_root_product,colorBlockEquiv_basis]
  rfl

end KhanSL2.SymmetricFamily
