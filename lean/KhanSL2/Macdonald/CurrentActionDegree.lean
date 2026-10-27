module

public import KhanSL2.Macdonald.SymmetricCoefficientsModule
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

/-! The actual degree-k symmetric powers are stable under the full current action
and under the raising coefficient operators. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

/-- A polynomial derivation whose values on variables have degree one preserves every degree. -/
theorem polynomialDerivation_preserves_degree (D : Derivation ℂ Poly Poly)
    (hX : ∀ m : Mode, D (MvPolynomial.X m) ∈ MvPolynomial.homogeneousSubmodule Mode ℂ 1)
    {k : ℕ} {p : Poly} (hp : p ∈ MvPolynomial.homogeneousSubmodule Mode ℂ k) :
    D p ∈ MvPolynomial.homogeneousSubmodule Mode ℂ k := by
  have hOne (q : Poly) (hq : q ∈ MvPolynomial.homogeneousSubmodule Mode ℂ 1) :
      D q ∈ MvPolynomial.homogeneousSubmodule Mode ℂ 1 := by
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X] at hq
    refine Submodule.span_induction ?_ ?_
      (fun u v _ _ hu hv => ?_) (fun c u _ hu => ?_) hq
    · rintro _ ⟨m,rfl⟩
      exact hX m
    · simp
    · rw [map_add]
      exact Submodule.add_mem _ hu hv
    · rw [Derivation.map_smul]
      exact Submodule.smul_mem _ c hu
  rw [← MvPolynomial.homogeneousSubmodule_one_pow] at hp ⊢
  induction hp using Submodule.pow_induction_on_left' with
  | algebraMap c => simp
  | add u v i hu hv ihu ihv =>
    rw [map_add]
    exact Submodule.add_mem _ ihu ihv
  | mem_mul q hq i p hp ih =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, pow_succ']
    apply Submodule.add_mem
    · exact Submodule.mul_mem_mul hq ih
    · rw [mul_comm p (D q)]
      exact Submodule.mul_mem_mul (hOne q hq) hp

/-- Every current variable is genuinely homogeneous of symmetric degree one. -/
theorem currentVariable_mem_degree_one (x : BGG.Current) :
    currentVariable x ∈ MvPolynomial.homogeneousSubmodule Mode ℂ 1 := by
  rw [currentVariable, Module.Basis.constr_apply]
  change ∑ m ∈ (symmetricCurrentBasis.repr x).support,
    symmetricCurrentBasis.repr x m • MvPolynomial.X m ∈ _
  apply Submodule.sum_mem
  intro m _
  exact Submodule.smul_mem _ _ (MvPolynomial.isHomogeneous_X ℂ m)

theorem symmetricDerivation_preserves_degree (D : Module.End ℂ BGG.Current)
    {k : ℕ} {p : Poly} (hp : p ∈ MvPolynomial.homogeneousSubmodule Mode ℂ k) :
    symmetricDerivation D p ∈ MvPolynomial.homogeneousSubmodule Mode ℂ k := by
  apply polynomialDerivation_preserves_degree _ _ hp
  intro m
  rw [symmetricDerivation_X]
  exact currentVariable_mem_degree_one _

/-- The degree-k symmetric power, with its actual inherited current representation. -/
def symmetricPower (k : ℕ) : LieSubmodule ℂ BGG.Current SymmetricCoefficients where
  toSubmodule := MvPolynomial.homogeneousSubmodule Mode ℂ k
  lie_mem {x _p} hp := symmetricDerivation_preserves_degree
    (LieAlgebra.ad ℂ BGG.Current x) hp

@[simp] theorem mem_symmetricPower (k : ℕ) (p : SymmetricCoefficients) :
    p ∈ symmetricPower k ↔ (symmetricCoefficientsEquiv p).IsHomogeneous k := Iff.rfl

/-- Each coefficient shift acts within a fixed symmetric power. -/
theorem symmetricCoefficientEnd_mem (m k : ℕ) {p : SymmetricCoefficients}
    (hp : p ∈ symmetricPower k) : symmetricCoefficientEnd m p ∈ symmetricPower k :=
  symmetricDerivation_preserves_degree (Modules.coefficientShift m) hp

/-- The raising power sum on the actual degree-k coefficient module. -/
def symmetricPowerCoefficientEnd (m k : ℕ) :
    symmetricPower k →ₗ⁅ℂ,BGG.Current⁆ symmetricPower k where
  toFun p := ⟨symmetricCoefficientEnd m p, symmetricCoefficientEnd_mem m k p.property⟩
  map_add' p q := by apply Subtype.ext; exact map_add (symmetricCoefficientEnd m) (p : SymmetricCoefficients) (q : SymmetricCoefficients)
  map_smul' c p := by apply Subtype.ext; exact map_smul (symmetricCoefficientEnd m) c (p : SymmetricCoefficients)
  map_lie' {x p} := by apply Subtype.ext; exact (symmetricCoefficientEnd m).map_lie x (p : SymmetricCoefficients)

end KhanSL2.Macdonald
