module

public import KhanSL2.BGG.CurrentBasis
public import KhanSL2.Modules.CoefficientOperators
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.MvPolynomial.Rename

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace KhanSL2.BGGBridge.TopAlternants

open Finset MvPolynomial BGG Current
open scoped TensorProduct

/-- The derivation of a wedge is the sum of its single-slot replacements. -/
theorem derivExt_ιMulti {M : Type*} [AddCommGroup M] [Module ℂ M]
    (D : Module.End ℂ M) (n : ℕ) (v : Fin n → M) :
    LieChains.derivExt D (ExteriorAlgebra.ιMulti ℂ n v) =
      ∑ i : Fin n, ExteriorAlgebra.ιMulti ℂ n (Function.update v i (D (v i))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply, LieChains.derivExt_ι_mul, ih,
      Finset.mul_sum, Fin.sum_univ_succ]
    congr 1
    · rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp only [Function.update_self, Matrix.vecTail,
        Function.update_comp_eq_of_forall_ne v (D (v 0)) (fun i => Fin.succ_ne_zero i)]
    · apply Finset.sum_congr rfl
      intro i _
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      simp only [Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i)), Matrix.vecTail,
        Function.update_comp_eq_of_injective v (Fin.succ_injective n) i, Function.comp_apply]

/-- A word consisting only of positive-root current modes. -/
def rootWord (B : ℕ) (a : Fin B → ℕ) : NB :=
  ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (a i, 0))

/-- Send a slot monomial to the corresponding ordered exterior word. -/
def rootPolynomialMap (B : ℕ) : MvPolynomial (Fin B) ℂ →ₗ[ℂ] NB :=
  Finsupp.linearCombination ℂ (fun d : Fin B →₀ ℕ => rootWord B d) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem rootPolynomialMap_monomial (B : ℕ) (d : Fin B →₀ ℕ) (c : ℂ) :
    rootPolynomialMap B (monomial d c) = c • rootWord B d :=
  Finsupp.linearCombination_single ℂ c d

@[simp] theorem rootPolynomialMap_product (B : ℕ) (a : Fin B → ℕ) :
    rootPolynomialMap B (∏ i : Fin B, (X i : MvPolynomial (Fin B) ℂ) ^ a i) =
      rootWord B a := by
  rw [MvPolynomial.prod_X_pow, rootPolynomialMap_monomial, one_smul]
  congr 1
  funext i
  simp

/-- The exterior word has the permutation sign of its slots. -/
theorem rootWord_perm (B : ℕ) (a : Fin B → ℕ) (e : Equiv.Perm (Fin B)) :
    rootWord B (a ∘ e) = e.sign • rootWord B a :=
  (ExteriorAlgebra.ιMulti ℂ B).map_perm (fun i => currentBasis (a i, 0)) e

/-- Renaming polynomial slots is carried to their exterior permutation sign. -/
theorem rootPolynomialMap_rename (B : ℕ) (e : Equiv.Perm (Fin B))
    (p : MvPolynomial (Fin B) ℂ) :
    rootPolynomialMap B (rename e p) = e.sign • rootPolynomialMap B p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [rename_monomial, rootPolynomialMap_monomial, rootPolynomialMap_monomial]
    have hd : (d.mapDomain e : Fin B → ℕ) = (fun i => d (e.symm i)) := by
      funext i
      exact Finsupp.mapDomain_equiv_apply d i
    rw [hd]
    change c • rootWord B (d ∘ e.symm) = _
    rw [rootWord_perm]
    simp only [Equiv.Perm.sign_symm]
    exact smul_comm _ _ _
  | add p q hp hq => simp only [map_add, hp, hq, smul_add]

@[simp] theorem coefficientShift_currentBasis (m n : ℕ) (a : Fin 3) :
    Modules.coefficientShift m (currentBasis (n, a)) = currentBasis (m + n, a) := by
  simp only [currentBasis_apply, mode_apply, Modules.coefficientShift_tmul, pow_add]

/-- The actual coefficient operator shifts each root word slot in turn. -/
theorem coefficientPower_rootWord (m B : ℕ) (a : Fin B → ℕ) :
    Modules.coefficientPower m (rootWord B a) =
      ∑ i : Fin B, rootWord B (Function.update a i (a i + m)) := by
  rw [rootWord, Modules.coefficientPower, derivExt_ιMulti]
  apply Finset.sum_congr rfl
  intro i _
  unfold rootWord
  congr 1
  funext j
  by_cases hij : j = i
  · subst j
    simp [Nat.add_comm, pow_add]
  · simp [Function.update_of_ne hij]

/-- Multiplying by the `m`th power sum is exactly the actual coefficient shift,
not an action transported from the desired isomorphism. -/
theorem rootPolynomialMap_powerSum (m B : ℕ) (p : MvPolynomial (Fin B) ℂ) :
    rootPolynomialMap B (psum (Fin B) ℂ m * p) =
      Modules.coefficientPower m (rootPolynomialMap B p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    simp only [psum, Finset.sum_mul, map_sum, X_pow_eq_monomial, monomial_mul,
      one_mul, rootPolynomialMap_monomial, map_smul, coefficientPower_rootWord,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    congr 1
    funext j
    by_cases hij : j = i
    · subst j
      simp [Nat.add_comm, pow_add]
    · simp [hij, Ne.symm hij, Function.update_of_ne hij]
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]

end KhanSL2.BGGBridge.TopAlternants
