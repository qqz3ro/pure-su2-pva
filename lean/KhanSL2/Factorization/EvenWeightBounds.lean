module

public import KhanSL2.BGG.Current
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators
namespace KhanSL2.Factorization.EvenWeightBounds

/-- The actual finite set of even Cartan weights from -2m through 2m. -/
def evenBoundPolynomial (m : ℕ) : Polynomial ℂ :=
  ∏ t : Fin (2*m+1), (X - C ((2 * ((t.val : ℤ) - (m : ℤ)) : ℤ) : ℂ))

theorem evenBoundPolynomial_eval_eq_zero_iff (m : ℕ) (μ : ℂ) :
    (evenBoundPolynomial m).eval μ = 0 ↔
      ∃ t : Fin (2*m+1), μ = ((2 * ((t.val : ℤ) - (m : ℤ)) : ℤ) : ℂ) := by
  simp [evenBoundPolynomial,Polynomial.eval_prod,Finset.prod_eq_zero_iff,sub_eq_zero]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A polynomial identity for an endomorphism constrains each actual nonzero eigenvector. -/
theorem eval_eq_zero_of_annihilator (T : Module.End ℂ V) (p : Polynomial ℂ)
    (hp : aeval T p = 0) (v : V) (hv : v ≠ 0) (μ : ℂ) (hμ : T v = μ • v) :
    p.eval μ = 0 := by
  have hs : p.eval μ • v = 0 := by
    rw [← Module.End.aeval_apply_of_mem_apply_eq_smul hμ,hp]
    rfl
  exact (smul_eq_zero.mp hs).resolve_right hv

/-- A natural highest weight killed by the even bounded polynomial is 2q with q≤m. -/
theorem naturalEigenvalue_even_bound (T : Module.End ℂ V) (m n : ℕ)
    (hp : aeval T (evenBoundPolynomial m) = 0)
    (v : V) (hv : v ≠ 0) (hn : T v = (n : ℂ) • v) :
    ∃ q : ℕ, q ≤ m ∧ n = 2*q := by
  have hz := eval_eq_zero_of_annihilator T (evenBoundPolynomial m) hp v hv (n : ℂ) hn
  obtain ⟨t,ht⟩ := (evenBoundPolynomial_eval_eq_zero_iff m (n : ℂ)).mp hz
  have hi : (n : ℤ) = 2 * ((t.val : ℤ) - (m : ℤ)) := by exact_mod_cast ht
  have htlt := t.isLt
  refine ⟨t.val-m,?_,?_⟩ <;> omega

/-- Excluding the top eigenspace makes the irreducible rank bound strict. -/
theorem naturalEigenvalue_even_strict_bound (T : Module.End ℂ V) (m n : ℕ)
    (hp : aeval T (evenBoundPolynomial m) = 0)
    (htop : T.eigenspace (2*(m : ℂ)) = ⊥)
    (v : V) (hv : v ≠ 0) (hn : T v = (n : ℂ) • v) :
    ∃ q : ℕ, q < m ∧ n = 2*q := by
  obtain ⟨q,hq,heq⟩ := naturalEigenvalue_even_bound T m n hp v hv hn
  refine ⟨q,?_,heq⟩
  by_contra hqm
  have hqm' : q = m := by omega
  have hmem : v ∈ T.eigenspace (2*(m : ℂ)) := by
    apply Module.End.mem_eigenspace_iff.mpr
    simpa only [heq,hqm',Nat.cast_mul,Nat.cast_ofNat] using hn
  rw [htop] at hmem
  exact hv hmem

/-- The Cartan endomorphism uses the same normalization as the actual colour tensor action. -/
abbrev cartan (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule BGG.G V] [LieModule ℂ BGG.G V] : Module.End ℂ V :=
  LieModule.toEnd ℂ BGG.G V MatrixSL2.h

end KhanSL2.Factorization.EvenWeightBounds