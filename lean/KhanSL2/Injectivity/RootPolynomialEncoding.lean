module

public import KhanSL2.Injectivity.RootCurrent
public import KhanSL2.Injectivity.OrderedProducts
public import KhanSL2.Injectivity.RootCycles
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Encoding root polynomials as finite exterior chains -/

@[expose] public section

noncomputable section

namespace KhanSL2.Injectivity.Cartan

open Finset

/-- A plus word followed by a minus word; both factors are in increasing slot order. -/
def rootWord {s : ℕ} (a b : Fin s → ℕ) : Cochain :=
  orderedProduct (fun i => generator (.plus (a i))) *
    orderedProduct (fun i => generator (.minus (b i)))

/-- Root monomials are interpreted as ordered exterior words.  Antisymmetrization
is supplied by the exterior product itself, so no factorial is divided out here. -/
def rootMonomial {s : ℕ} (d : (Fin s ⊕ Fin s) →₀ ℕ) : Cochain :=
  rootWord (fun i => d (.inl i)) (fun i => d (.inr i))

def rootEncode (s : ℕ) : MvPolynomial (Fin s ⊕ Fin s) ℂ →ₗ[ℂ] Cochain :=
  Finsupp.linearCombination ℂ rootMonomial ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem rootEncode_monomial {s : ℕ} (d : (Fin s ⊕ Fin s) →₀ ℕ) (c : ℂ) :
    rootEncode s (MvPolynomial.monomial d c) = c • rootMonomial d := by
  exact Finsupp.linearCombination_single ℂ c d

theorem generator_update {s : ℕ} (color : ℕ → Mode) (a : Fin s → ℕ) (i : Fin s) (j : ℕ) :
    (fun t => generator (color (Function.update a i j t))) =
      Function.update (fun t => generator (color (a t))) i (generator (color j)) := by
  funext t
  by_cases h : t = i
  · subst t; simp
  · simp [Function.update_of_ne h]

theorem rootCurrentAction_plusWord {s : ℕ} (k : ℕ) (a : Fin s → ℕ) :
    rootCurrentAction k (orderedProduct (fun i => generator (.plus (a i)))) =
      ∑ i, orderedProduct (fun t => generator (.plus (Function.update a i (a i + k) t))) := by
  rw [linearMap_orderedProduct _ (rootCurrentAction_mul k) (rootCurrentAction_one k)]
  apply sum_congr rfl
  intro i _hi
  rw [rootCurrentAction_generator, rootCurrentGenerator, generator_update]

theorem rootCurrentAction_minusWord {s : ℕ} (k : ℕ) (b : Fin s → ℕ) :
    rootCurrentAction k (orderedProduct (fun i => generator (.minus (b i)))) =
      -∑ i, orderedProduct (fun t => generator (.minus (Function.update b i (b i + k) t))) := by
  rw [linearMap_orderedProduct _ (rootCurrentAction_mul k) (rootCurrentAction_one k),
    ← sum_neg_distrib]
  apply sum_congr rfl
  intro i _hi
  rw [rootCurrentAction_generator, rootCurrentGenerator, orderedProduct_update_neg,
    generator_update]

theorem rootCurrentAction_rootWord {s : ℕ} (k : ℕ) (a b : Fin s → ℕ) :
    rootCurrentAction k (rootWord a b) =
      (∑ i, rootWord (Function.update a i (a i + k)) b) -
        ∑ i, rootWord a (Function.update b i (b i + k)) := by
  simp only [rootWord, rootCurrentAction_mul, rootCurrentAction_plusWord,
    rootCurrentAction_minusWord, sum_mul, mul_neg, mul_sum, sub_eq_add_neg]

/-- The polynomial encoding of the Cartan current of index `k`. -/
def rootCurrentPolynomial (s k : ℕ) : MvPolynomial (Fin s ⊕ Fin s) ℂ :=
  (∑ i : Fin s, MvPolynomial.X (Sum.inl i : Fin s ⊕ Fin s) ^ k) -
    ∑ i : Fin s, MvPolynomial.X (Sum.inr i : Fin s ⊕ Fin s) ^ k

theorem rootCurrentPolynomial_eq_powerSum (s k : ℕ) :
    rootCurrentPolynomial s k =
      rootPowerSum (fun i : Fin s => (MvPolynomial.X (Sum.inl i) :
        MvPolynomial (Fin s ⊕ Fin s) ℂ)) k -
      rootPowerSum (fun i : Fin s => (MvPolynomial.X (Sum.inr i) :
        MvPolynomial (Fin s ⊕ Fin s) ℂ)) k := by
  simp only [rootCurrentPolynomial, rootPowerSum_eq_sum]

theorem rootMonomial_shift_plus {s : ℕ} (d : (Fin s ⊕ Fin s) →₀ ℕ)
    (i : Fin s) (k : ℕ) :
    rootMonomial (Finsupp.single (.inl i) k + d) =
      rootWord (Function.update (fun t => d (.inl t)) i (d (.inl i) + k))
        (fun t => d (.inr t)) := by
  unfold rootMonomial
  congr 1
  · funext t
    by_cases h : t = i
    · subst t; simp [Nat.add_comm]
    · simp [Finsupp.single_apply, h, Ne.symm h]
  · funext t
    simp

theorem rootMonomial_shift_minus {s : ℕ} (d : (Fin s ⊕ Fin s) →₀ ℕ)
    (i : Fin s) (k : ℕ) :
    rootMonomial (Finsupp.single (.inr i) k + d) =
      rootWord (fun t => d (.inl t))
        (Function.update (fun t => d (.inr t)) i (d (.inr i) + k)) := by
  unfold rootMonomial
  congr 1
  · funext t
    simp
  · funext t
    by_cases h : t = i
    · subst t; simp [Nat.add_comm]
    · simp [Finsupp.single_apply, h, Ne.symm h]

/-- Multiplication by a power-sum difference is the actual root-current action
on the ordered exterior-chain encoding. -/
theorem rootCurrentAction_rootEncode {s : ℕ} (k : ℕ)
    (P : MvPolynomial (Fin s ⊕ Fin s) ℂ) :
    rootCurrentAction k (rootEncode s P) = rootEncode s (rootCurrentPolynomial s k * P) := by
  refine MvPolynomial.induction_on' P ?_ ?_
  · intro d c
    rw [rootEncode_monomial, map_smul, rootMonomial, rootCurrentAction_rootWord]
    simp only [rootCurrentPolynomial, sub_mul, sum_mul, map_sub, map_sum,
      ← MvPolynomial.monomial_single_add, rootEncode_monomial,
      rootMonomial_shift_plus, rootMonomial_shift_minus, smul_sub, Finset.smul_sum]
  · intro P Q hP hQ
    simp only [map_add, mul_add, hP, hQ]

end KhanSL2.Injectivity.Cartan
