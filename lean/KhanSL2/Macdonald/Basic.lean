module

public import KhanSL2.BGG.PolynomialKoszul
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

/-! The concrete mixed algebra for the sl2 strong Macdonald calculation.

The same finite mode labels index two different kinds of variables: `sigma a n`
has polynomial mode n (including zero), while `psi a i` has positive mode i+1.
Only the underlying tensor-monomial algebra of `PolynomialKoszul` is reused;
its differential and its positive polynomial-mode grading are not used here.
-/

noncomputable section
open scoped BigOperators TensorProduct

namespace KhanSL2.Macdonald

abbrev Mode := BGG.PositiveCE.Mode
abbrev Poly := MvPolynomial Mode ℂ
abbrev Exterior := BGG.PositiveCE.Cochain
abbrev W := Poly ⊗[ℂ] Exterior
abbrev Exponent := Mode →₀ ℕ
abbrev BasisIndex := Exponent × Finset Mode

/-- The actual tensor-monomial basis, with finite polynomial and exterior support. -/
def basis : Module.Basis BasisIndex ℂ W := BGG.PolynomialKoszul.basis

@[simp] theorem basis_apply (s : Exponent) (t : Finset Mode) :
    basis (s, t) = MvPolynomial.monomial s 1 ⊗ₜ[ℂ] FiniteExterior.monomial t :=
  BGG.PolynomialKoszul.basis_apply s t

/-- The even variable of physical mode n, including the zero mode. -/
def sigma (a : Fin 3) (n : ℕ) : W :=
  MvPolynomial.X (⟨n, a⟩ : Mode) ⊗ₜ[ℂ] (1 : Exterior)

/-- The odd variable of physical mode i+1. There is no odd zero mode. -/
def psi (a : Fin 3) (i : ℕ) : W :=
  (1 : Poly) ⊗ₜ[ℂ] FiniteExterior.generator (⟨i, a⟩ : Mode)

/-- Every even coordinate is central in the mixed algebra. -/
theorem sigma_commute (a : Fin 3) (n : ℕ) (u : W) :
    sigma a n * u = u * sigma a n := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul p v => simp [sigma, Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add u v hu hv => simp only [mul_add, add_mul, hu, hv]

theorem sigma_comm (a b : Fin 3) (n m : ℕ) :
    sigma a n * sigma b m = sigma b m * sigma a n :=
  sigma_commute a n _

/-- The odd coordinates anticommute with their actual exterior signs. -/
theorem psi_anticomm (a b : Fin 3) (i j : ℕ) :
    psi a i * psi b j = -(psi b j * psi a i) := by
  have h := FiniteExterior.wedge_generator_supercomm
    BGG.PositiveCE.Mode.code BGG.PositiveCE.Mode.code_injective
    (⟨i, a⟩ : Mode) (FiniteExterior.generator (⟨j, b⟩ : Mode))
  change FiniteExterior.generator (⟨i, a⟩ : Mode) *
      FiniteExterior.generator (⟨j, b⟩ : Mode) =
    FiniteExterior.parityLinear (FiniteExterior.generator (⟨j, b⟩ : Mode)) *
      FiniteExterior.generator (⟨i, a⟩ : Mode) at h
  simp only [FiniteExterior.parity_generator, neg_mul] at h
  simpa only [psi, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    TensorProduct.tmul_neg] using congrArg (fun v : Exterior => (1 : Poly) ⊗ₜ[ℂ] v) h

end KhanSL2.Macdonald
