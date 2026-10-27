module

public import KhanSL2.SymmetricFamily.CoefficientAction
public import KhanSL2.PolynomialBGG.RootRingFree
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Finite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! The actual symmetric current coefficient modules are finite projective
over the fixed coefficient ring, through their normalized labelled-tensor retract. -/

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Macdonald PolynomialBGG Conditional
open scoped KhanSL2.Conditional

/-- Symmetrization as a map over the actual coefficient ring. -/
def symmetricToTensorLinear (k : ℕ) :
    symmetricPower k →ₗ[CoefficientRing k] (⨂[ℂ]^k BGG.Current) where
  __ := (symmetricToTensor k).toAddHom
  map_smul' := symmetricToTensor_smul k

/-- Actual symmetric multiplication as a map over the same coefficient ring. -/
def tensorToSymmetricLinear (k : ℕ) :
    (⨂[ℂ]^k BGG.Current) →ₗ[CoefficientRing k] symmetricPower k where
  __ := (tensorToSymmetric k).toAddHom
  map_smul' := tensorToSymmetric_smul k

/-- The normalized coefficient-linear tensor retract. -/
theorem symmetric_tensor_split (k : ℕ) :
    (tensorToSymmetricLinear k).comp (symmetricToTensorLinear k) = LinearMap.id := by
  apply LinearMap.ext
  intro p
  exact tensorToSymmetric_symmetricToTensor k p

/-- The labelled ambient current tensors form a finite free coefficient module. -/
theorem currentTensor_free (k : ℕ) : Module.Free (CoefficientRing k) (⨂[ℂ]^k BGG.Current) :=
  Module.Free.of_equiv (rootTensorLinearEquiv k).symm

theorem currentTensor_finite (k : ℕ) : Module.Finite (CoefficientRing k) (⨂[ℂ]^k BGG.Current) := by
  have := Module.Finite.trans (R := CoefficientRing k) (RootPolynomial k)
    (RootPolynomial k ⊗[ℂ] Color k)
  exact Module.Finite.equiv (rootTensorLinearEquiv k).symm

/-- Actual degree-k symmetric current coefficients are projective over R_k. -/
theorem symmetricPower_projective (k : ℕ) : Module.Projective (CoefficientRing k) (symmetricPower k) := by
  let := currentTensor_free k
  exact Module.Projective.of_split (symmetricToTensorLinear k) (tensorToSymmetricLinear k)
    (symmetric_tensor_split k)

/-- Actual degree-k symmetric current coefficients are finitely generated over R_k. -/
theorem symmetricPower_finite (k : ℕ) : Module.Finite (CoefficientRing k) (symmetricPower k) := by
  let := currentTensor_finite k
  apply Module.Finite.of_surjective (tensorToSymmetricLinear k)
  intro p
  exact ⟨symmetricToTensor k p,tensorToSymmetric_symmetricToTensor k p⟩

end KhanSL2.SymmetricFamily
