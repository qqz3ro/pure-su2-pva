module

public import KhanSL2.BGG.FreeCE
public import KhanSL2.BGG.PolynomialKoszul

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! PBW comparison of the actual free CE differential with the polynomial Koszul differential. -/

noncomputable section
open scoped TensorProduct BigOperators

namespace KhanSL2.BGG.PBWLeading

open MvPolynomial TauCeti.UniversalEnvelopingAlgebra

variable {R L I : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder I]
  (b : Module.Basis I R L)

/-- PBW evaluation respects the actual word filtration. -/
theorem eval_word_mem (l : List L) :
    b.pbwEval (l.map (UniversalEnvelopingAlgebra.ι R)).prod ∈
      restrictTotalDegree I R l.length := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, Module.Basis.pbwEval_one, mem_restrictTotalDegree,
      totalDegree_one]
    exact Nat.zero_le _
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, Module.Basis.pbwEval_ι_mul, List.length_cons]
    exact b.pbwPolynomialRep_mem_restrictTotalDegree x ih

theorem eval_mem {n : ℕ} {u : UniversalEnvelopingAlgebra R L}
    (hu : u ∈ pbwFiltration R L n) : b.pbwEval u ∈ restrictTotalDegree I R n := by
  have h : pbwFiltration R L n ≤ (restrictTotalDegree I R n).comap b.pbwEval :=
    (pbwFiltration_le_iff R L).mpr fun l hl =>
      restrictTotalDegree_mono I R hl (eval_word_mem b l)
  exact h hu

/-- Right multiplication has the same leading polynomial term, with an error one degree lower. -/
theorem eval_right_word_error (l : List I) (i : I) :
    b.pbwEval (pbwMonomial R L b l * UniversalEnvelopingAlgebra.ι R (b i)) -
        X i * b.pbwEval (pbwMonomial R L b l) ∈ restrictTotalDegree I R l.length := by
  have hp : (l ++ [i]).Perm (i :: l) := List.perm_append_comm
  have hc := pbwMonomial_sub_pbwMonomial_mem_pbwFiltrationPrevious_of_perm R L b hp
  simp only [List.length_append, List.length_singleton, pbwFiltrationPrevious_succ,
    pbwMonomial_append, pbwMonomial_cons, pbwMonomial_nil, mul_one] at hc
  have hce := eval_mem b hc
  rw [map_sub] at hce
  have hw : b.pbwEval (pbwMonomial R L b l) ∈ restrictTotalDegree I R l.length := by
    rw [pbwMonomial_def]
    simpa only [List.length_map] using eval_word_mem b (l.map b)
  have he := b.pbwPolynomialRep_sub_mul_mem_restrictTotalDegree (b i) hw
  rw [Module.Basis.constr_basis, ← Module.Basis.pbwEval_ι_mul] at he
  simpa only [sub_add_sub_cancel] using (restrictTotalDegree I R l.length).add_mem hce he

/-- The strict leading-term estimate on each genuine ordered PBW basis vector. -/
theorem eval_right_basis_error (s : I →₀ ℕ) (i : I) :
    b.pbwEval (b.pbwBasis s * UniversalEnvelopingAlgebra.ι R (b i)) -
        X i * MvPolynomial.monomial s 1 ∈ restrictTotalDegree I R (s.sum fun _ n => n) := by
  have h := eval_right_word_error b (s.toMultiset.sort (· ≤ ·)) i
  rw [← Module.Basis.pbwBasis_apply] at h
  simp only [Module.Basis.pbwEval_pbwBasis, Multiset.length_sort, Finsupp.card_toMultiset] at h
  have hs : (s.sum fun _ => id) = s.sum (fun _ n => n) := by
    apply Finsupp.sum_congr
    intro j hj
    rfl
  rw [hs] at h
  exact h

end KhanSL2.BGG.PBWLeading

namespace KhanSL2.BGG.FreeCE

attribute [local instance] FiniteExterior.codeOrder

/-- The actual right-action correction in positive-current PBW polynomial coordinates. -/
theorem polynomialEquiv_right_error (s : Mode →₀ ℕ) (m : Mode) :
    polynomialEquiv (polynomialEquiv.symm (MvPolynomial.monomial s 1) * ueGenerator m) -
        MvPolynomial.X m * MvPolynomial.monomial s 1 ∈
      MvPolynomial.restrictTotalDegree Mode ℂ (s.sum fun _ n => n) := by
  simpa only [polynomialEquiv, Module.Basis.pbwEquiv_symm_monomial,
    Module.Basis.pbwEquiv_apply, positiveColorBasis_apply, ueGenerator] using
    PBWLeading.eval_right_basis_error positiveColorBasis s m

/-- Tensor the actual PBW equivalence with the existing exterior model. -/
def chainPolynomialEquiv : Chain ≃ₗ[ℂ] PolynomialKoszul.Chain :=
  TensorProduct.congr polynomialEquiv (LinearEquiv.refl ℂ Cochain)

@[simp] theorem chainPolynomialEquiv_tmul (u : PositiveEnveloping) (ω : Cochain) :
    chainPolynomialEquiv (u ⊗ₜ[ℂ] ω) = polynomialEquiv u ⊗ₜ[ℂ] ω := by
  simp only [chainPolynomialEquiv, TensorProduct.congr_tmul, LinearEquiv.refl_apply]

@[simp] theorem chainPolynomialEquiv_symm_tmul (p : MvPolynomial Mode ℂ) (ω : Cochain) :
    chainPolynomialEquiv.symm (p ⊗ₜ[ℂ] ω) = polynomialEquiv.symm p ⊗ₜ[ℂ] ω := by
  apply chainPolynomialEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, chainPolynomialEquiv_tmul,
    LinearEquiv.apply_symm_apply]

/-- The full CE differential in polynomial coordinates, with no change to its actual operator. -/
def polynomialDifferential : Module.End ℂ PolynomialKoszul.Chain :=
  chainPolynomialEquiv.toLinearMap.comp
    ((differential.restrictScalars ℂ).comp chainPolynomialEquiv.symm.toLinearMap)

theorem polynomialDifferential_tmul_monomial (p : MvPolynomial Mode ℂ) (s : Finset Mode) :
    polynomialDifferential (p ⊗ₜ[ℂ] FiniteExterior.monomial s) =
      (∑ m ∈ s, polynomialEquiv (polynomialEquiv.symm p * ueGenerator m) ⊗ₜ[ℂ]
        PositiveCE.contract m (FiniteExterior.monomial s)) +
          p ⊗ₜ[ℂ] PositiveCE.boundary (FiniteExterior.monomial s) := by
  change chainPolynomialEquiv (differential (chainPolynomialEquiv.symm
    (p ⊗ₜ[ℂ] FiniteExterior.monomial s))) = _
  rw [chainPolynomialEquiv_symm_tmul, differential_tmul, action_tmul_monomial, map_add, map_sum]
  simp only [chainPolynomialEquiv_tmul, LinearEquiv.apply_symm_apply]

/-- The error relative to Koszul is explicitly the lower-PBW action error plus the bracket boundary. -/
theorem polynomialDifferential_sub_koszul_basis (s : Mode →₀ ℕ) (t : Finset Mode) :
    (polynomialDifferential - PolynomialKoszul.d) (PolynomialKoszul.basis (s,t)) =
      (∑ m ∈ t,
        (polynomialEquiv (polynomialEquiv.symm (MvPolynomial.monomial s 1) * ueGenerator m) -
          MvPolynomial.X m * MvPolynomial.monomial s 1) ⊗ₜ[ℂ]
            PositiveCE.contract m (FiniteExterior.monomial t)) +
      MvPolynomial.monomial s 1 ⊗ₜ[ℂ] PositiveCE.boundary (FiniteExterior.monomial t) := by
  rw [LinearMap.sub_apply, PolynomialKoszul.d_basis, PolynomialKoszul.basis_apply,
    polynomialDifferential_tmul_monomial]
  simp only [PolynomialKoszul.basis_apply, PolynomialKoszul.dTerm_tmul,
    TensorProduct.sub_tmul, Finset.sum_sub_distrib]
  abel

end KhanSL2.BGG.FreeCE
