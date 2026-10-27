module

public import KhanSL2.Macdonald.CurrentActionDegree
public import KhanSL2.Macdonald.CurrentActionFunctorial
public import Mathlib.Algebra.Lie.TensorProduct

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The actual primitive coproduct on symmetric current coefficients. It is
current-equivariant and every raising coefficient operator is a coderivation.
The exterior CE shuffle is a separate construction. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald

/-- The primitive coproduct, expressed directly in polynomial coordinates. -/
def symmetricCoproductAlg : SymmetricCoefficients →ₐ[ℂ]
    SymmetricCoefficients ⊗[ℂ] SymmetricCoefficients :=
  MvPolynomial.aeval (fun m : Mode =>
    (show SymmetricCoefficients from MvPolynomial.X m) ⊗ₜ[ℂ] 1 +
      1 ⊗ₜ[ℂ] (show SymmetricCoefficients from MvPolynomial.X m))

@[simp] theorem symmetricCoproductAlg_X (m : Mode) :
    symmetricCoproductAlg (show SymmetricCoefficients from MvPolynomial.X m) =
      (show SymmetricCoefficients from MvPolynomial.X m) ⊗ₜ[ℂ] 1 +
        1 ⊗ₜ[ℂ] (show SymmetricCoefficients from MvPolynomial.X m) :=
  MvPolynomial.aeval_X _ _

/-- Every actual current generator is primitive. -/
theorem symmetricCoproduct_currentVariable (x : BGG.Current) :
    symmetricCoproductAlg (show SymmetricCoefficients from currentVariable x) =
      (show SymmetricCoefficients from currentVariable x) ⊗ₜ[ℂ] 1 +
        1 ⊗ₜ[ℂ] (show SymmetricCoefficients from currentVariable x) := by
  let v : BGG.Current →ₗ[ℂ] SymmetricCoefficients := currentVariable
  have h : symmetricCoproductAlg.toLinearMap.comp v =
      ((TensorProduct.mk ℂ SymmetricCoefficients SymmetricCoefficients).flip 1).comp v +
        (TensorProduct.mk ℂ SymmetricCoefficients SymmetricCoefficients 1).comp v := by
    apply symmetricCurrentBasis.ext
    intro m
    change symmetricCoproductAlg (show SymmetricCoefficients from
      currentVariable (symmetricCurrentBasis m)) =
      (show SymmetricCoefficients from currentVariable (symmetricCurrentBasis m)) ⊗ₜ[ℂ] 1 +
        1 ⊗ₜ[ℂ] (show SymmetricCoefficients from currentVariable (symmetricCurrentBasis m))
    rw [currentVariable_basis, symmetricCoproductAlg_X]
  exact LinearMap.congr_fun h x

/-- The sum of a derivation acting in each tensor factor. -/
def symmetricTensorDerivation (D : Derivation ℂ SymmetricCoefficients SymmetricCoefficients) :
    Derivation ℂ (SymmetricCoefficients ⊗[ℂ] SymmetricCoefficients)
      (SymmetricCoefficients ⊗[ℂ] SymmetricCoefficients) :=
  Derivation.mk' (D.toLinearMap.rTensor SymmetricCoefficients +
    D.toLinearMap.lTensor SymmetricCoefficients) (by
    intro u v
    induction u using TensorProduct.induction_on with
    | zero => simp
    | add u u' hu hu' =>
      simp only [add_mul, map_add, hu, hu', add_smul, smul_add]
      abel
    | tmul p q =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v v' hv hv' =>
        simp only [mul_add, map_add, hv, hv', add_smul, smul_add]
        abel
      | tmul r s =>
        simp only [LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, Derivation.coeFn_coe, Derivation.leibniz, smul_eq_mul,
          TensorProduct.add_tmul, TensorProduct.tmul_add, add_mul, mul_add,
          Algebra.TensorProduct.tmul_mul_tmul]
        rw [mul_comm s q, mul_comm r p]
        abel)

@[simp] theorem symmetricTensorDerivation_tmul
    (D : Derivation ℂ SymmetricCoefficients SymmetricCoefficients)
    (p q : SymmetricCoefficients) :
    symmetricTensorDerivation D (p ⊗ₜ[ℂ] q) = D p ⊗ₜ[ℂ] q + p ⊗ₜ[ℂ] D q := rfl

/-- Every linearly extended current-space endomorphism is a coderivation. -/
theorem symmetricCoproduct_symmetricDerivation (D : Module.End ℂ BGG.Current)
    (p : SymmetricCoefficients) :
    symmetricCoproductAlg (show SymmetricCoefficients from symmetricDerivation D p) =
      symmetricTensorDerivation (show Derivation ℂ SymmetricCoefficients SymmetricCoefficients
        from symmetricDerivation D) (symmetricCoproductAlg p) := by
  have hX (m : Mode) : symmetricCoproductAlg
      (show SymmetricCoefficients from symmetricDerivation D (MvPolynomial.X m)) =
      symmetricTensorDerivation (show Derivation ℂ SymmetricCoefficients SymmetricCoefficients
        from symmetricDerivation D)
          (symmetricCoproductAlg (show SymmetricCoefficients from MvPolynomial.X m)) := by
    have hOne : (show Derivation ℂ SymmetricCoefficients SymmetricCoefficients
        from symmetricDerivation D) 1 = 0 := Derivation.map_one_eq_zero _
    have hVar : (show Derivation ℂ SymmetricCoefficients SymmetricCoefficients
        from symmetricDerivation D) (show SymmetricCoefficients from MvPolynomial.X m) =
        (show SymmetricCoefficients from currentVariable (D (symmetricCurrentBasis m))) :=
      symmetricDerivation_X D m
    rw [symmetricDerivation_X, symmetricCoproduct_currentVariable, symmetricCoproductAlg_X]
    simp only [map_add, symmetricTensorDerivation, Derivation.coe_mk',
      LinearMap.add_apply, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul,
      Derivation.coeFn_coe, hOne, hVar,
      TensorProduct.zero_tmul, TensorProduct.tmul_zero, add_zero, zero_add,
      symmetricDerivation_X]
  exact polynomialDerivation_intertwines symmetricCoproductAlg (symmetricDerivation D)
    (symmetricTensorDerivation (show Derivation ℂ SymmetricCoefficients SymmetricCoefficients
      from symmetricDerivation D)) hX p

/-- Tensor extension of the adjoint action is the standard diagonal tensor Lie action. -/
theorem symmetricTensorDerivation_currentAction (x : BGG.Current)
    (t : SymmetricCoefficients ⊗[ℂ] SymmetricCoefficients) :
    symmetricTensorDerivation (show Derivation ℂ SymmetricCoefficients SymmetricCoefficients
      from currentAction x) t = ⁅x,t⁆ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t u ht hu => simp only [map_add, ht, hu, lie_add]
  | tmul p q => rfl

/-- The primitive coproduct is a morphism of the actual current representations. -/
def symmetricCoproduct : SymmetricCoefficients →ₗ⁅ℂ,BGG.Current⁆
    SymmetricCoefficients ⊗[ℂ] SymmetricCoefficients where
  toLinearMap := symmetricCoproductAlg.toLinearMap
  map_lie' {x p} := by
    exact (symmetricCoproduct_symmetricDerivation (LieAlgebra.ad ℂ BGG.Current x) p).trans
      (symmetricTensorDerivation_currentAction x _)

/-- Explicit coefficient coderivation identity, with the actual raising operators. -/
theorem symmetricCoproduct_coefficientEnd (m : ℕ) (p : SymmetricCoefficients) :
    symmetricCoproduct (symmetricCoefficientEnd m p) =
      ((symmetricCoefficientEnd m).toLinearMap.rTensor SymmetricCoefficients +
        (symmetricCoefficientEnd m).toLinearMap.lTensor SymmetricCoefficients)
          (symmetricCoproduct p) :=
  symmetricCoproduct_symmetricDerivation (Modules.coefficientShift m) p

end KhanSL2.Macdonald
