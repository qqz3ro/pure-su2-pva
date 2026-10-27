module

public import KhanSL2.SymmetricFamily.UncoloredTensor
public import KhanSL2.SymmetricFamily.DerivationProduct
public import KhanSL2.Macdonald.CurrentActionDegree

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The actual one-color symmetric polynomial algebra used for the even free
Macdonald generators, with its specified raising derivation. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace KhanSL2.Macdonald
open SymmetricFamily PolynomialBGG

abbrev RootEvenPolynomial := MvPolynomial ℕ ℂ
abbrev RootEvenPower (r : ℕ) := MvPolynomial.homogeneousSubmodule ℕ ℂ r

/-- Regard a one-variable polynomial as a linear combination of symmetric generators. -/
def rootEvenVariable : Polynomial ℂ →ₗ[ℂ] RootEvenPolynomial :=
  (Polynomial.basisMonomials ℂ).constr ℂ MvPolynomial.X

@[simp] theorem rootEvenVariable_basis (n : ℕ) :
    rootEvenVariable (Polynomial.basisMonomials ℂ n) = MvPolynomial.X n :=
  Module.Basis.constr_basis _ _ _ _

@[simp] theorem rootEvenVariable_X_pow (n : ℕ) :
    rootEvenVariable ((Polynomial.X : Polynomial ℂ)^n) = MvPolynomial.X n := by
  simpa only [Polynomial.coe_basisMonomials, ← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.C_1,one_mul] using rootEvenVariable_basis n

/-- Raise a free even generator's index by m, before the weight-two scalar. -/
def rootEvenShift (m : ℕ) : Derivation ℂ RootEvenPolynomial RootEvenPolynomial :=
  MvPolynomial.mkDerivation ℂ (fun n => MvPolynomial.X (m+n))

@[simp] theorem rootEvenShift_X (m n : ℕ) :
    rootEvenShift m (MvPolynomial.X n) = MvPolynomial.X (m+n) :=
  MvPolynomial.mkDerivation_X _ _ _

theorem rootEvenShift_variable (m : ℕ) (p : Polynomial ℂ) :
    rootEvenShift m (rootEvenVariable p) =
      rootEvenVariable ((Polynomial.X : Polynomial ℂ)^m * p) := by
  have h : (rootEvenShift m).toLinearMap.comp rootEvenVariable =
      rootEvenVariable.comp (LinearMap.mulLeft ℂ ((Polynomial.X : Polynomial ℂ)^m)) := by
    apply (Polynomial.basisMonomials ℂ).ext
    intro n
    simp only [LinearMap.comp_apply, Derivation.coeFn_coe, rootEvenVariable_basis,
      rootEvenShift_X, Polynomial.coe_basisMonomials, ← Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.C_1,one_mul,LinearMap.mulLeft_apply,← pow_add,rootEvenVariable_X_pow]
  exact LinearMap.congr_fun h p

/-- The original homogeneous polynomial coefficients, without normalization. -/
def rootEvenExponentEquiv (r : ℕ) : RootEvenPower r ≃ₗ[ℂ] ExponentSpace ℕ r :=
  (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported ℕ ℂ r)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp {d : ℕ →₀ ℕ | d.degree = r})

@[simp] theorem rootEvenExponentEquiv_symm_single (r : ℕ)
    (d : DegreeExponent ℕ r) (c : ℂ) :
    ((rootEvenExponentEquiv r).symm (Finsupp.single d c)).val =
      MvPolynomial.monomial d.val c := by
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := ℂ) {e : ℕ →₀ ℕ | e.degree = r}).symm
      (Finsupp.single d c) : Finsupp.supported ℂ ℂ {e : ℕ →₀ ℕ | e.degree = r}) :
      (ℕ →₀ ℕ) →₀ ℂ) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- Multiply the symmetric variables associated to the actual polynomial tensor slots. -/
def rootEvenTensorProduct (r : ℕ) :
    (⨂[ℂ]^r (Polynomial ℂ)) →ₗ[ℂ] RootEvenPolynomial :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin r) RootEvenPolynomial).compLinearMap
    (fun _ => rootEvenVariable))

@[simp] theorem rootEvenTensorProduct_tprod (r : ℕ) (v : Fin r → Polynomial ℂ) :
    rootEvenTensorProduct r (PiTensorProduct.tprod ℂ v) = ∏ i, rootEvenVariable (v i) := by
  simp only [rootEvenTensorProduct, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

/-- Symmetric multiplication in the actual homogeneous power. -/
def rootTensorToEven (r : ℕ) : (⨂[ℂ]^r (Polynomial ℂ)) →ₗ[ℂ] RootEvenPower r :=
  (rootEvenExponentEquiv r).symm.toLinearMap.comp
    ((unlabel r).comp (polynomialWordBasis r).repr.toLinearMap)

@[simp] theorem rootTensorToEven_basis (r : ℕ) (u : Fin r → ℕ) :
    (rootTensorToEven r (polynomialWordBasis r u)).val =
      MvPolynomial.monomial (wordExponent u) 1 := by
  simp only [rootTensorToEven, LinearMap.comp_apply,LinearEquiv.coe_coe,
    Module.Basis.repr_self,unlabel_single,rootEvenExponentEquiv_symm_single]
  rfl

theorem rootTensorToEven_coe (r : ℕ) (x : ⨂[ℂ]^r (Polynomial ℂ)) :
    (rootTensorToEven r x).val = rootEvenTensorProduct r x := by
  have h : (RootEvenPower r).subtype.comp (rootTensorToEven r) = rootEvenTensorProduct r := by
    apply (polynomialWordBasis r).ext
    intro u
    change (rootTensorToEven r (polynomialWordBasis r u)).val = _
    rw [rootTensorToEven_basis,polynomialWordBasis_apply,rootEvenTensorProduct_tprod]
    simp only [rootEvenVariable_X_pow,wordExponent_eq_sum_single,MvPolynomial.monomial_sum_one]
    rfl
  exact LinearMap.congr_fun h x

/-- The specified normalized invariant word map to symmetric root polynomials. -/
def rootEvenPolynomialEquiv (r : ℕ) :
    RootEvenPower r ≃ₗ[ℂ] MvPolynomial.symmetricSubalgebra (Fin r) ℂ :=
  (rootEvenExponentEquiv r).trans (exponentSymmetricPolynomialEquiv r)

end KhanSL2.Macdonald
