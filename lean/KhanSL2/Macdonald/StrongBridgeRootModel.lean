module

public import KhanSL2.Macdonald.StrongBridgeNormalization
public import KhanSL2.SymmetricFamily.UncoloredExterior
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Algebra.Polynomial.Basis

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Explicit root-polynomial coordinates for the free Macdonald homology model.
Odd indices give alternating polynomials; even multiplicities give symmetric
polynomials. The maps use the specified normalized monomial bases throughout. -/
noncomputable section
open scoped TensorProduct DirectSum
namespace KhanSL2.Macdonald
open SymmetricFamily

/-- q odd generators and r even generators, of coefficient degree q+2r. -/
def FreeBidegreeIndex (q r : ℕ) :=
  {b : FreeMonomialIndex // b.1.degree = r ∧ b.2.card = q}

/-- The polynomial module occurring in the symmetric relative homology formula. -/
abbrev RootHomologyModel (q r : ℕ) :=
  alternatingRootPolynomials q ⊗[ℂ] MvPolynomial.symmetricSubalgebra (Fin r) ℂ

/-- The actual uncolored exterior basis, in increasing order of exponents. -/
def alternatingRootBasis (q : ℕ) :
    Module.Basis (Set.powersetCard ℕ q) ℂ (alternatingRootPolynomials q) :=
  ((Polynomial.basisMonomials ℂ).exteriorPower q).map (exteriorPolynomialEquiv q)

/-- The actual normalized symmetric monomial basis of the even root ring. -/
def symmetricRootBasis (r : ℕ) :
    Module.Basis (DegreeExponent ℕ r) ℂ (MvPolynomial.symmetricSubalgebra (Fin r) ℂ) :=
  Finsupp.basisSingleOne.map (exponentSymmetricPolynomialEquiv r)

def freeBidegreeIndexEquiv (q r : ℕ) :
    FreeBidegreeIndex q r ≃ (Set.powersetCard ℕ q) × (DegreeExponent ℕ r) where
  toFun b := (⟨b.val.2,b.property.2⟩,⟨b.val.1,b.property.1⟩)
  invFun b := ⟨(b.2.val,b.1.val),b.2.property,b.1.property⟩
  left_inv _b := rfl
  right_inv _b := rfl

/-- Monomial coordinates become the actual alternating/symmetric root-polynomial module. -/
def freeBidegreeRootEquiv (q r : ℕ) :
    (FreeBidegreeIndex q r →₀ ℂ) ≃ₗ[ℂ] RootHomologyModel q r :=
  (Finsupp.domLCongr (freeBidegreeIndexEquiv q r)).trans
    ((alternatingRootBasis q).tensorProduct (symmetricRootBasis r)).repr.symm

@[simp] theorem freeBidegreeRootEquiv_single (q r : ℕ)
    (b : FreeBidegreeIndex q r) (c : ℂ) :
    freeBidegreeRootEquiv q r (Finsupp.single b c) =
      c • ((alternatingRootBasis q) (freeBidegreeIndexEquiv q r b).1 ⊗ₜ[ℂ]
        (symmetricRootBasis r) (freeBidegreeIndexEquiv q r b).2) := by
  simp only [freeBidegreeRootEquiv, LinearEquiv.trans_apply, Finsupp.domLCongr_single,
    Module.Basis.repr_symm_single]
  congr 1
  exact Module.Basis.tensorProduct_apply _ _ _ _

/-- Every free monomial has a unique odd/even bidegree. -/
def freeBidegreePartitionEquiv :
    (Σ d : ℕ × ℕ, FreeBidegreeIndex d.1 d.2) ≃ FreeMonomialIndex where
  toFun b := b.2.val
  invFun b := ⟨(b.2.card,b.1.degree),⟨b,rfl,rfl⟩⟩
  left_inv b := by
    obtain ⟨⟨q,r⟩,b,hb⟩ := b
    rcases hb with ⟨he,ho⟩
    dsimp only
    cases he
    cases ho
    rfl
  right_inv _b := rfl

/-- Assemble the explicit root-polynomial modules with finite support. -/
def freeRootModelEquiv : (FreeMonomialIndex →₀ ℂ) ≃ₗ[ℂ]
    ⨁ d : ℕ × ℕ, RootHomologyModel d.1 d.2 :=
  (Finsupp.domLCongr freeBidegreePartitionEquiv.symm).trans
    ((sigmaFinsuppLequivDFinsupp ℂ).trans
      (DFinsupp.mapRange.linearEquiv (fun d : ℕ × ℕ => freeBidegreeRootEquiv d.1 d.2)))

/-- The actual relative homology of all symmetric coefficients, with explicit
factorial normalization, as alternating/symmetric root polynomials. -/
def strongTotalHomologyRootEquiv :
    Factorization.TotalHomology SymmetricCoefficients ≃ₗ[ℂ]
      ⨁ d : ℕ × ℕ, RootHomologyModel d.1 d.2 :=
  strongTotalHomologyFreeEquiv.trans (strongFreeUncoloredEquiv.trans freeRootModelEquiv)

end KhanSL2.Macdonald
