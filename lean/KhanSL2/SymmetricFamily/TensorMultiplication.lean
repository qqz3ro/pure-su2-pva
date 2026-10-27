module

public import KhanSL2.SymmetricFamily.TensorWords
public import Mathlib.LinearAlgebra.Multilinear.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The normalized invariant-tensor equivalence has the actual symmetric
multiplication map as its inverse. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open Macdonald

/-- Multiply actual current variables in the symmetric algebra. -/
def tensorProductPolynomial (k : ℕ) : (⨂[ℂ]^k BGG.Current) →ₗ[ℂ] Poly :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin k) Poly).compLinearMap
    (fun _ => currentVariable))

@[simp] theorem tensorProductPolynomial_tprod (k : ℕ) (v : Fin k → BGG.Current) :
    tensorProductPolynomial k (PiTensorProduct.tprod ℂ v) = ∏ i, currentVariable (v i) := by
  simp only [tensorProductPolynomial, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- The symmetric quotient in homogeneous polynomial coordinates. -/
def tensorToSymmetric (k : ℕ) : (⨂[ℂ]^k BGG.Current) →ₗ[ℂ] symmetricPower k :=
  (symmetricExponentEquiv k).symm.toLinearMap.comp
    ((unlabel k).comp (currentWordBasis k).repr.toLinearMap)

@[simp] theorem tensorToSymmetric_basis (k : ℕ) (u : Fin k → Macdonald.Mode) :
    (tensorToSymmetric k (currentWordBasis k u) : SymmetricCoefficients) =
      MvPolynomial.monomial (wordExponent u) 1 := by
  simp only [tensorToSymmetric, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Module.Basis.repr_self, unlabel_single, symmetricExponentEquiv_symm_single]
  rfl

/-- The coordinate quotient is exactly multiplication of symmetric current variables. -/
theorem tensorToSymmetric_coe (k : ℕ) (x : ⨂[ℂ]^k BGG.Current) :
    (tensorToSymmetric k x : SymmetricCoefficients) = tensorProductPolynomial k x := by
  have h : (symmetricPower k).toSubmodule.subtype.comp (tensorToSymmetric k) =
      (show (⨂[ℂ]^k BGG.Current) →ₗ[ℂ] SymmetricCoefficients from tensorProductPolynomial k) := by
    apply (currentWordBasis k).ext
    intro u
    change (tensorToSymmetric k (currentWordBasis k u) : SymmetricCoefficients) = _
    rw [tensorToSymmetric_basis, currentWordBasis_apply]
    change (MvPolynomial.monomial (wordExponent u) 1 : Poly) =
      tensorProductPolynomial k (PiTensorProduct.tprod ℂ (fun i => symmetricCurrentBasis (u i)))
    rw [tensorProductPolynomial_tprod]
    simp only [currentVariable_basis, wordExponent_eq_sum_single, MvPolynomial.monomial_sum_one]
    rfl
  exact LinearMap.congr_fun h x

/-- The homogeneous quotient has the expected value on arbitrary pure tensors. -/
theorem tensorToSymmetric_tprod (k : ℕ) (v : Fin k → BGG.Current) :
    (tensorToSymmetric k (PiTensorProduct.tprod ℂ v) : SymmetricCoefficients) =
      ∏ i, currentVariable (v i) := by
  rw [tensorToSymmetric_coe, tensorProductPolynomial_tprod]

/-- The actual normalized symmetrization map, with values in all labelled tensors. -/
def symmetricToTensor (k : ℕ) : symmetricPower k →ₗ[ℂ] (⨂[ℂ]^k BGG.Current) :=
  (currentWordBasis k).repr.symm.toLinearMap.comp
    ((relabel k).comp (symmetricExponentEquiv k).toLinearMap)

theorem symmetricToTensor_mem (k : ℕ) (p : symmetricPower k) :
    symmetricToTensor k p ∈ invariantTensors k := by
  change (currentWordBasis k).repr
    ((currentWordBasis k).repr.symm (relabel k (symmetricExponentEquiv k p))) ∈ invariantWords k
  rw [LinearEquiv.apply_symm_apply]
  exact relabel_mem k _

/-- Multiplication after normalized symmetrization is the identity. -/
@[simp] theorem tensorToSymmetric_symmetricToTensor (k : ℕ) (p : symmetricPower k) :
    tensorToSymmetric k (symmetricToTensor k p) = p := by
  apply (symmetricExponentEquiv k).injective
  simp only [tensorToSymmetric, symmetricToTensor, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, unlabel_relabel]

/-- On invariant tensors normalized symmetrization after multiplication is the identity. -/
theorem symmetricToTensor_tensorToSymmetric (k : ℕ) (x : ⨂[ℂ]^k BGG.Current)
    (hx : x ∈ invariantTensors k) :
    symmetricToTensor k (tensorToSymmetric k x) = x := by
  apply (currentWordBasis k).repr.injective
  simp only [tensorToSymmetric, symmetricToTensor, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  exact (relabel_unlabel k _).trans (wordAverage_eq_self hx)

end KhanSL2.SymmetricFamily
