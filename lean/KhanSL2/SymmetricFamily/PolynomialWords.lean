module

public import KhanSL2.SymmetricFamily.WordInvariants
public import KhanSL2.Macdonald.CurrentActionDegree
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The existing actual symmetric coefficient power, in its homogeneous
monomial coordinates and normalized invariant-word coordinates. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open Macdonald

/-- Restriction to the degree-k monomial support of the actual polynomial module. -/
def symmetricExponentEquiv (k : ℕ) : symmetricPower k ≃ₗ[ℂ] ExponentSpace Macdonald.Mode k := by
  change (MvPolynomial.homogeneousSubmodule Macdonald.Mode ℂ k) ≃ₗ[ℂ] ExponentSpace Macdonald.Mode k
  exact (LinearEquiv.ofEq _ _
    (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported Macdonald.Mode ℂ k)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp {d : Macdonald.Mode →₀ ℕ | d.degree = k})

/-- A coordinate singleton is the specified polynomial monomial, with no scalar rescaling. -/
@[simp] theorem symmetricExponentEquiv_symm_single (k : ℕ)
    (d : DegreeExponent Macdonald.Mode k) (c : ℂ) :
    ((symmetricExponentEquiv k).symm (Finsupp.single d c) : SymmetricCoefficients) =
      (show SymmetricCoefficients from MvPolynomial.monomial d.val c) := by
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := ℂ) {e : Macdonald.Mode →₀ ℕ | e.degree = k}).symm
      (Finsupp.single d c) : Finsupp.supported ℂ ℂ {e : Macdonald.Mode →₀ ℕ | e.degree = k}) :
      (Macdonald.Mode →₀ ℕ) →₀ ℂ) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- Symmetric coefficient monomials identify with invariant labelled mode-color words. -/
def symmetricWordEquiv (k : ℕ) : symmetricPower k ≃ₗ[ℂ] invariantWords (α := Macdonald.Mode) k :=
  (symmetricExponentEquiv k).trans (exponentInvariantEquiv k)

end KhanSL2.SymmetricFamily
