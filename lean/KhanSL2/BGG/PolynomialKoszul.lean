module

public import KhanSL2.BGG.PositiveBoundaryAdjoint
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Algebra.Algebra.Bilinear

@[expose] public section

/-! The polynomial Koszul differential and Euler homotopy on the actual tensor
of polynomials with the concrete exterior algebra. All defining sums are finite. -/

noncomputable section
open scoped BigOperators TensorProduct
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PolynomialKoszul

abbrev Mode := PositiveCE.Mode
abbrev Poly := MvPolynomial Mode ℂ
abbrev Exterior := PositiveCE.Cochain
abbrev Chain := Poly ⊗[ℂ] Exterior
abbrev Exponent := Mode →₀ ℕ
abbrev BasisIndex := Exponent × Finset Mode

/-- The tensor-monomial basis of the polynomial exterior module. -/
def basis : Module.Basis BasisIndex ℂ Chain :=
  (MvPolynomial.basisMonomials Mode ℂ).tensorProduct
    (Finsupp.basisSingleOne : Module.Basis (Finset Mode) ℂ Exterior)

@[simp] theorem basis_apply (s : Exponent) (t : Finset Mode) :
    basis (s,t) = MvPolynomial.monomial s 1 ⊗ₜ[ℂ] monomial t := by
  simp [basis, monomial]

/-- Polynomial degree plus exterior degree, the filtration preserved by the Koszul operators. -/
def totalLength (b : BasisIndex) : ℕ := b.1.sum (fun _ n => n) + b.2.card

abbrev polynomialMultiply (i : Mode) : Module.End ℂ Poly :=
  LinearMap.mul ℂ Poly (MvPolynomial.X i)

abbrev exteriorMultiply (i : Mode) : Module.End ℂ Exterior :=
  FiniteExterior.wedgeLinear PositiveCE.Mode.code (FiniteExterior.generator i)

/-- One multiplication/contraction term of the Koszul differential. -/
def dTerm (i : Mode) : Module.End ℂ Chain :=
  TensorProduct.map (polynomialMultiply i) (PositiveCE.contract i)

/-- One derivative/creation term of the unnormalized Euler homotopy. -/
def hTerm (i : Mode) : Module.End ℂ Chain :=
  TensorProduct.map (MvPolynomial.pderiv i).toLinearMap (exteriorMultiply i)

@[simp] theorem dTerm_tmul (i : Mode) (p : Poly) (u : Exterior) :
    dTerm i (p ⊗ₜ[ℂ] u) = (MvPolynomial.X i * p) ⊗ₜ[ℂ] PositiveCE.contract i u := rfl

@[simp] theorem hTerm_tmul (i : Mode) (p : Poly) (u : Exterior) :
    hTerm i (p ⊗ₜ[ℂ] u) = MvPolynomial.pderiv i p ⊗ₜ[ℂ] (FiniteExterior.generator i * u) := rfl

/-- The genuine Koszul differential, defined using the finite exterior support of each basis vector. -/
def d : Module.End ℂ Chain :=
  basis.constr ℂ (fun b => ∑ i∈b.2, dTerm i (basis b))

/-- The genuine Euler homotopy, defined using the finite polynomial support of each basis vector. -/
def H : Module.End ℂ Chain :=
  basis.constr ℂ (fun b => ∑ i∈b.1.support, hTerm i (basis b))

@[simp] theorem d_basis (b : BasisIndex) : d (basis b) = ∑ i∈b.2, dTerm i (basis b) :=
  basis.constr_basis ℂ _ b

@[simp] theorem H_basis (b : BasisIndex) : H (basis b) = ∑ i∈b.1.support, hTerm i (basis b) :=
  basis.constr_basis ℂ _ b

/-- Finite cutoffs used in algebraic calculations. -/
def finiteD (S : Finset Mode) : Module.End ℂ Chain := ∑ i∈S, dTerm i

def finiteH (S : Finset Mode) : Module.End ℂ Chain := ∑ i∈S, hTerm i

@[simp] theorem finiteD_apply (S : Finset Mode) (u : Chain) :
    finiteD S u = ∑ i∈S, dTerm i u := by simp [finiteD, LinearMap.sum_apply]

@[simp] theorem finiteH_apply (S : Finset Mode) (u : Chain) :
    finiteH S u = ∑ i∈S, hTerm i u := by simp [finiteH, LinearMap.sum_apply]

/-- The polynomial and exterior diagonal number operators for one variable. -/
def polynomialNumber (i : Mode) : Module.End ℂ Chain :=
  TensorProduct.map ((polynomialMultiply i).comp (MvPolynomial.pderiv i).toLinearMap) LinearMap.id

def exteriorNumber (i : Mode) : Module.End ℂ Chain :=
  TensorProduct.map LinearMap.id ((exteriorMultiply i).comp (PositiveCE.contract i))

@[simp] theorem polynomialNumber_tmul (i : Mode) (p : Poly) (u : Exterior) :
    polynomialNumber i (p ⊗ₜ[ℂ] u) =
      (MvPolynomial.X i * MvPolynomial.pderiv i p) ⊗ₜ[ℂ] u := rfl

@[simp] theorem exteriorNumber_tmul (i : Mode) (p : Poly) (u : Exterior) :
    exteriorNumber i (p ⊗ₜ[ℂ] u) =
      p ⊗ₜ[ℂ] (FiniteExterior.generator i * PositiveCE.contract i u) := rfl

private theorem generators_anticomm (i j : Mode) :
    FiniteExterior.generator i * FiniteExterior.generator j =
      -(FiniteExterior.generator j * FiniteExterior.generator i) := by
  have h := wedge_generator_supercomm PositiveCE.Mode.code PositiveCE.Mode.code_injective i (FiniteExterior.generator j)
  change FiniteExterior.generator i * FiniteExterior.generator j =
    parityLinear (FiniteExterior.generator j) * FiniteExterior.generator i at h
  simpa only [parity_generator, neg_mul] using h

/-- Contractions anticommute, proved using their genuine coefficient transposes. -/
theorem contracts_anticomm (i j : Mode) (u : Exterior) :
    PositiveCE.contract i (PositiveCE.contract j u) =
      -PositiveCE.contract j (PositiveCE.contract i u) := by
  apply eq_neg_iff_add_eq_zero.mpr
  apply PositiveCE.coefficientPairing_left_nondegenerate
  intro v
  simp only [map_add, LinearMap.add_apply]
  have hc (k : Mode) (x y : Exterior) : coefficientPairing (PositiveCE.contract k x) y =
      coefficientPairing x (FiniteExterior.generator k * y) :=
    coefficientPairing_contraction (α := Mode) k x y
  rw [hc, hc, hc, hc, ← mul_assoc, generators_anticomm j i, neg_mul, map_neg, mul_assoc]
  ring

/-- The creation/annihilation relation, including the polynomial product rule. -/
theorem dTerm_hTerm (i j : Mode) :
    (dTerm i).comp (hTerm j) + (hTerm j).comp (dTerm i) =
      if i=j then polynomialNumber i + exteriorNumber i else 0 := by
  apply TensorProduct.ext'
  intro p u
  simp only [LinearMap.add_apply, LinearMap.comp_apply, dTerm_tmul, hTerm_tmul]
  have hc : PositiveCE.contract i (FiniteExterior.generator j * u) =
      (if i=j then u else 0) - FiniteExterior.generator j * PositiveCE.contract i u :=
    contraction_generator_wedge PositiveCE.Mode.code PositiveCE.Mode.code_injective i j u
  rw [hc, MvPolynomial.pderiv_mul]
  by_cases h : i=j
  · subst j
    simp only [ite_true, MvPolynomial.pderiv_X_self, one_mul, LinearMap.add_apply,
      polynomialNumber_tmul, exteriorNumber_tmul, TensorProduct.tmul_sub,
      TensorProduct.add_tmul]
    abel
  · simp only [if_neg h, MvPolynomial.pderiv_X_of_ne h, zero_mul, zero_add,
      zero_sub, TensorProduct.tmul_neg, LinearMap.zero_apply]
    abel

/-- The differential summands anticommute. -/
theorem dTerms_anticomm (i j : Mode) :
    (dTerm i).comp (dTerm j) = -((dTerm j).comp (dTerm i)) := by
  apply TensorProduct.ext'
  intro p u
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, dTerm_tmul]
  rw [contracts_anticomm i j, TensorProduct.tmul_neg]
  congr 2
  exact mul_left_comm _ _ _

/-- The homotopy summands anticommute. -/
theorem hTerms_anticomm (i j : Mode) :
    (hTerm i).comp (hTerm j) = -((hTerm j).comp (hTerm i)) := by
  apply TensorProduct.ext'
  intro p u
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, hTerm_tmul]
  rw [MvPolynomial.pderiv_comm i j, ← mul_assoc, generators_anticomm i j,
    neg_mul, mul_assoc, TensorProduct.tmul_neg]

end KhanSL2.BGG.PolynomialKoszul
