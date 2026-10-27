module

public import KhanSL2.SymmetricFamily.ColorWeights
public import KhanSL2.Factorization.EvenWeightBoundsBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Explicit polynomial annihilators for the actual finite color action and
for every scalar multiplicity space. These bounds pass to the later fibres and
subquotients through equivariant maps. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Factorization.EvenWeightBounds

/-- The actual Cartan action on color tensors has only even weights in [-2k,2k]. -/
theorem colorCartan_annihilator (k : ℕ) :
    Polynomial.aeval (colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h))
      (evenBoundPolynomial k) = 0 :=
  evenBoundPolynomial_annihilates_of_basis
    (Pi.basisFun ℂ (Fin k → Fin 3)) _ k colorWordHalfWeight
    (colorCartan_basis k)
    (fun c => (colorWordHalfWeight_bounds c).1)
    (fun c => (colorWordHalfWeight_bounds c).2)

/-- Adding any multiplicity space leaves the genuine even Cartan bound unchanged. -/
theorem rootColorCartan_annihilator (k : ℕ) (Q : Type*) [AddCommGroup Q] [Module ℂ Q] :
    Polynomial.aeval
      (LinearMap.lTensor Q (colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h)))
      (evenBoundPolynomial k) = 0 := by
  let b := (Module.Free.chooseBasis ℂ Q).tensorProduct (Pi.basisFun ℂ (Fin k → Fin 3))
  apply evenBoundPolynomial_annihilates_of_basis b _ k (fun i => colorWordHalfWeight i.2)
  · rintro ⟨i,c⟩
    simp only [b, Module.Basis.tensorProduct_apply, LinearMap.lTensor_tmul,
      colorCartan_basis, TensorProduct.tmul_smul]
  · intro i
    exact (colorWordHalfWeight_bounds i.2).1
  · intro i
    exact (colorWordHalfWeight_bounds i.2).2

end KhanSL2.SymmetricFamily
