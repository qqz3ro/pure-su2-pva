module

public import KhanSL2.Macdonald.PolynomialPairing

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Finite vector-field formulas for actual polynomial derivations. -/
noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

/-- A finite sum of coefficient-weighted partial derivatives. -/
def finiteVectorField (S : Finset Mode) (f : Mode → Poly) : Derivation ℂ Poly Poly :=
  ∑ i ∈ S, f i • MvPolynomial.pderiv i

@[simp] theorem finiteVectorField_apply (S : Finset Mode) (f : Mode → Poly) (p : Poly) :
    finiteVectorField S f p = ∑ i ∈ S, f i * MvPolynomial.pderiv i p := by
  simp [finiteVectorField, smul_eq_mul]

theorem finiteVectorField_X (S : Finset Mode) (f : Mode → Poly) (i : Mode) (hi : i ∈ S) :
    finiteVectorField S f (MvPolynomial.X i) = f i := by
  classical
  simp [finiteVectorField_apply, MvPolynomial.pderiv_X, Pi.single_apply, hi]

/-- Any cutoff containing the variables of p gives its exact derivation value. -/
theorem polynomialDerivation_apply_finite (D : Derivation ℂ Poly Poly)
    (S : Finset Mode) (p : Poly) (hp : p.vars ⊆ S) :
    D p = ∑ i ∈ S, D (MvPolynomial.X i) * MvPolynomial.pderiv i p := by
  rw [← finiteVectorField_apply]
  apply MvPolynomial.derivation_eq_of_forall_mem_vars
  intro i hi
  exact (finiteVectorField_X S (fun j => D (MvPolynomial.X j)) i (hp hi)).symm

/-- Transposition of an arbitrary finite linear vector field, with all coefficients explicit. -/
theorem polynomialPairing_finite_vectorField (S T : Finset Mode)
    (a : Mode → Mode → ℂ) (p q : Poly) :
    polynomialPairing
      (∑ i ∈ S, ∑ j ∈ T, a i j • (MvPolynomial.X j * MvPolynomial.pderiv i p)) q =
    polynomialPairing p
      (∑ j ∈ T, ∑ i ∈ S, a i j • (MvPolynomial.X i * MvPolynomial.pderiv j q)) := by
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    polynomialPairing_vectorField]
  exact Finset.sum_comm

end KhanSL2.Macdonald
