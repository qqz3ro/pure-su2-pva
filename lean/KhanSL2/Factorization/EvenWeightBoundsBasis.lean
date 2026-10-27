module

public import KhanSL2.Factorization.EvenWeightBounds

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
namespace KhanSL2.Factorization.EvenWeightBounds

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A polynomial that vanishes on every eigenvalue of a diagonal basis annihilates
the actual endomorphism. The indexing type need not be finite. -/
theorem annihilator_of_eigenbasis {ι : Type*} (b : Module.Basis ι ℂ V)
    (T : Module.End ℂ V) (μ : ι → ℂ)
    (hT : ∀ i, T (b i) = μ i • b i) (p : Polynomial ℂ)
    (hp : ∀ i, p.eval (μ i) = 0) : aeval T p = 0 := by
  apply b.ext
  intro i
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hT i), hp i, zero_smul]
  rfl

/-- The explicit bounded polynomial vanishes at every even weight in the interval. -/
theorem evenBoundPolynomial_eval_twice_int (m : ℕ) (w : ℤ)
    (hlo : -(m : ℤ) ≤ w) (hhi : w ≤ m) :
    (evenBoundPolynomial m).eval (2*(w : ℂ)) = 0 := by
  apply (evenBoundPolynomial_eval_eq_zero_iff m _).mpr
  have hnonneg : 0 ≤ w + m := by omega
  have hlt : (w + m).toNat < 2*m+1 := by omega
  refine ⟨⟨(w+m).toNat,hlt⟩,?_⟩
  have heq : ((w+m).toNat : ℤ) - m = w := by omega
  rw [heq]
  norm_cast

/-- A diagonal basis with even weights between -2m and 2m supplies the concrete
polynomial annihilator used by all subsequent subquotient and rank bounds. -/
theorem evenBoundPolynomial_annihilates_of_basis {ι : Type*}
    (b : Module.Basis ι ℂ V) (T : Module.End ℂ V) (m : ℕ) (w : ι → ℤ)
    (hT : ∀ i, T (b i) = (2*(w i : ℂ)) • b i)
    (hlo : ∀ i, -(m : ℤ) ≤ w i) (hhi : ∀ i, w i ≤ m) :
    aeval T (evenBoundPolynomial m) = 0 :=
  annihilator_of_eigenbasis b T (fun i => 2*(w i : ℂ)) hT _
    (fun i => evenBoundPolynomial_eval_twice_int m (w i) (hlo i) (hhi i))

end KhanSL2.Factorization.EvenWeightBounds
