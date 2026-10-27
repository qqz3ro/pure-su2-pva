module

public import KhanSL2.SymmetricFamily.SymmetricBlockCoproduct
public import KhanSL2.SymmetricFamily.CoproductWords

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The generic normalization formula applied to the original current
symmetric powers and their actual homogeneous coproduct. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.SymmetricFamily
open Macdonald

/-- Labelled polynomial multiplication is the original current tensor quotient. -/
theorem polynomialWordMap_current (k : ℕ) (z : ⨂[ℂ]^k BGG.Current) :
    polynomialWordMap k ((currentWordBasis k).repr z) = tensorProductPolynomial k z := by
  have h : (polynomialWordMap k).comp (currentWordBasis k).repr.toLinearMap =
      tensorProductPolynomial k := by
    apply (currentWordBasis k).ext
    intro u
    change polynomialWordMap k ((currentWordBasis k).repr (currentWordBasis k u)) =
      tensorProductPolynomial k (currentWordBasis k u)
    rw [Module.Basis.repr_self,polynomialWordMap_single,one_smul,
      currentWordBasis_apply,tensorProductPolynomial_tprod]
    simp only [currentVariable_basis,subsetPolynomial]
  exact LinearMap.congr_fun h z

/-- Multiplication of one block of the original normalized labelled current tensor. -/
def symmetricBlockPolynomial {k r : ℕ} (S : Assignment k r) :
    symmetricPower k →ₗ[ℂ] Poly ⊗[ℂ] Poly :=
  (polynomialBlockWordMap S).comp
    ((currentWordBasis k).repr.toLinearMap.comp (symmetricToTensor k))

/-- The exact binomial factor for the original normalized symmetric section. -/
theorem symmetricBlockPolynomial_normalization {k r : ℕ}
    (S : Assignment k r) (p : symmetricPower k) :
    polynomialPrimitiveComponent k r (p.val : Poly) =
      (Nat.choose k r : ℂ) • symmetricBlockPolynomial S p := by
  have h := polynomialPrimitiveComponent_normalized S
    ((currentWordBasis k).repr (symmetricToTensor k p))
  have ha : wordAverage k ((currentWordBasis k).repr (symmetricToTensor k p)) =
      (currentWordBasis k).repr (symmetricToTensor k p) :=
    wordAverage_eq_self (symmetricToTensor_mem k p)
  rw [ha,polynomialWordMap_current] at h
  have hp : tensorProductPolynomial k (symmetricToTensor k p) = (p.val : Poly) :=
    (tensorToSymmetric_coe k (symmetricToTensor k p)).symm.trans
      (congrArg Subtype.val (tensorToSymmetric_symmetricToTensor k p))
  rw [hp] at h
  exact h

/-- The generic primitive polynomial component is the original bundled current coproduct. -/
theorem symmetricCoproductComponent_polynomial (r t : ℕ)
    (p : symmetricPower (r+t)) :
    TensorProduct.map (symmetricPower r).toSubmodule.subtype
      (symmetricPower t).toSubmodule.subtype (symmetricCoproductComponent r t p) =
      polynomialPrimitiveComponent (r+t) r (p.val : Poly) := by
  rw [symmetricCoproductComponent_apply]
  change TensorProduct.map (symmetricPower r).toSubmodule.subtype
    (symmetricPower t).toSubmodule.subtype
      (TensorProduct.map (symmetricPowerProjection r).toLinearMap
        (symmetricPowerProjection t).toLinearMap
          (symmetricCoproductAlg (p.val : Poly))) = _
  change ((TensorProduct.map (symmetricPower r).toSubmodule.subtype
    (symmetricPower t).toSubmodule.subtype).comp
      (TensorProduct.map (symmetricPowerProjection r).toLinearMap
        (symmetricPowerProjection t).toLinearMap)) (symmetricCoproductAlg (p.val : Poly)) = _
  rw [← TensorProduct.map_comp]
  simp only [polynomialPrimitiveComponent,Nat.add_sub_cancel_left,LinearMap.comp_apply]
  rfl

/-- The actual fixed-degree coproduct, in unchanged polynomial coordinates,
is exactly the stated scalar multiple of normalized block multiplication. -/
theorem symmetricCoproductComponent_normalization (r t : ℕ)
    (S : Assignment (r+t) r) (p : symmetricPower (r+t)) :
    TensorProduct.map (symmetricPower r).toSubmodule.subtype
      (symmetricPower t).toSubmodule.subtype (symmetricCoproductComponent r t p) =
        (Nat.choose (r+t) r : ℂ) • symmetricBlockPolynomial S p := by
  rw [symmetricCoproductComponent_polynomial,symmetricBlockPolynomial_normalization S p]

end KhanSL2.SymmetricFamily
