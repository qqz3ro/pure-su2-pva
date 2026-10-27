module

public import KhanSL2.Injectivity.RootClosedFamilies
public import KhanSL2.Injectivity.CartanBlockDeterminant
public import KhanSL2.Injectivity.RootAlternation

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace KhanSL2.Injectivity

open Finset

theorem sum_piFinset_succ {A B : Type*} [DecidableEq A] [AddCommMonoid B]
    {n : ℕ} (S : Fin (n + 1) → Finset A) (f : (Fin (n + 1) → A) → B) :
    (∑ j ∈ Fintype.piFinset S, f j) =
      ∑ x ∈ S 0, ∑ j ∈ Fintype.piFinset (Fin.tail S), f (Fin.cons x j) := by
  rw [← sum_product (S 0) (Fintype.piFinset (Fin.tail S))
    (fun x => f (Fin.cons x.1 x.2))]
  apply sum_bij (fun j _ => (j 0, Fin.tail j))
  · intro j hj
    simp only [mem_product, Fintype.mem_piFinset] at *
    exact ⟨hj 0, fun i => hj i.succ⟩
  · intro a _ha b _hb hab
    have h0 := congrArg Prod.fst hab
    have ht := congrArg Prod.snd hab
    funext i
    refine Fin.cases h0 (fun j => congrFun ht j) i
  · rintro ⟨x, j⟩ hj
    refine ⟨Fin.cons x j, ?_, ?_⟩
    · simp only [mem_product, Fintype.mem_piFinset] at hj ⊢
      intro i
      refine Fin.cases hj.1 (fun k => hj.2 k) i
    · simp
  · intro j _hj
    simp

namespace Cartan

open MvPolynomial

def cartanTensor (s : ℕ) : {r : ℕ} → (Fin r → ℕ →₀ RootPolynomial s) →
    RootPolynomial s → Cochain
  | 0, _, p => rootEncode s p
  | r + 1, θ, p => ∑ j ∈ (θ 0).support,
      generator (.cartan (j - 1)) * cartanTensor s (r := r) (Fin.tail θ) (θ 0 j * p)

theorem cartanTensor_eq_newtonFamily {s r : ℕ} (e : Fin r → ℕ) (p : RootPolynomial s) :
    cartanTensor s (fun i => rootTheta s (e i)) p =
      (newtonFamily s (List.ofFn e)).toLinearMap p := by
  induction r generalizing p with
  | zero => simp [cartanTensor, newtonFamily, rootFamily]
  | succ r ih =>
    rw [List.ofFn_succ, newtonFamily_cons]
    unfold cartanTensor
    apply sum_congr rfl
    intro j _hj
    simp only [Fin.tail_def]
    rw [ih]

theorem cartanTensor_expansion {s r : ℕ} (θ : Fin r → ℕ →₀ RootPolynomial s)
    (p : RootPolynomial s) :
    cartanTensor s θ p =
      ∑ j ∈ Fintype.piFinset (fun i => (θ i).support),
        orderedProduct (fun i => generator (.cartan (j i - 1))) *
          rootEncode s ((∏ i, θ i (j i)) * p) := by
  induction r generalizing p with
  | zero =>
    have hset : Fintype.piFinset (fun i : Fin 0 => (θ i).support) = Finset.univ := by
      ext j
      simp only [Fintype.mem_piFinset, mem_univ, iff_true]
      intro i
      exact Fin.elim0 i
    rw [hset]
    simp [cartanTensor]
  | succ r ih =>
    rw [sum_piFinset_succ]
    unfold cartanTensor
    apply sum_congr rfl
    intro j _hj
    rw [ih, mul_sum]
    apply sum_congr rfl
    intro js _hjs
    simp only [orderedProduct_succ, Fin.cons_zero, Fin.tail_def, Fin.cons_succ,
      Fin.prod_univ_succ]
    rw [mul_assoc]
    congr 2
    congr 1
    ring

def prefixedRootEncode {r s : ℕ} (a : Fin r ⊕ Fin s → ℕ) (b : Fin r → ℕ) :
    RootPolynomial s →ₗ[ℂ] Cochain :=
  (FiniteExterior.wedgeLinear Mode.code
    (orderedProduct (fun i => generator (.neutral (a (finSumFinEquiv.symm i)))))).comp
    ((FiniteExterior.wedgeLinear Mode.code (orderedProduct (fun i => generator (.cartan (b i))))).comp
      (rootEncode s))

theorem chainPolynomial_prefixedRootEncode {r s : ℕ}
    (a : Fin r ⊕ Fin s → ℕ) (b : Fin r → ℕ) (p : RootPolynomial s) :
    chainPolynomial r s (prefixedRootEncode a b p) =
      (sourceOrderingSign r s : EvaluationPolynomial r s) *
        (Matrix.det (fun i j : Fin r ⊕ Fin s => X j ^ a i) *
          (Matrix.det (fun i j : Fin r => ((b i + 1 : ℕ) : EvaluationPolynomial r s) *
            X (.inl j) ^ b i) * rootAlternation (fun i : Fin s => X (.inr i)) p)) := by
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro d c
    change chainPolynomial r s
      (orderedProduct (fun i => generator (.neutral (a (finSumFinEquiv.symm i)))) *
        (orderedProduct (fun i => generator (.cartan (b i))) * rootEncode s (monomial d c))) = _
    rw [rootEncode_monomial, mul_smul_comm, mul_smul_comm, map_smul]
    change c • chainPolynomial r s (fullWord a b (fun i => d (.inl i)) (fun i => d (.inr i))) = _
    rw [chainPolynomial_fullWord, rootAlternation_monomial]
    simp only [mul_smul_comm]
  · intro p q hp hq
    simp only [map_add, hp, hq, mul_add]

end Cartan
end KhanSL2.Injectivity
