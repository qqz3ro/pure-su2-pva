module

public import KhanSL2.BGGBridge.TopAlternantsMap
public import KhanSL2.BGGBridge.TopWeightBasis

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace KhanSL2.PolynomialBGG

open Finset MvPolynomial BGG Current BGGBridge
open scoped TensorProduct

/-- An ordered coefficient wedge with arbitrary current-root colors. -/
def coloredWord (B : ℕ) (c : Fin B → Fin 3) (a : Fin B → ℕ) : NB :=
  ExteriorAlgebra.ιMulti ℂ B (fun i => currentBasis (a i, c i))

/-- Labelled polynomial monomials record the modes of the colored exterior word. -/
def coloredPolynomialMap (B : ℕ) (c : Fin B → Fin 3) :
    MvPolynomial (Fin B) ℂ →ₗ[ℂ] NB :=
  Finsupp.linearCombination ℂ (fun d : Fin B →₀ ℕ => coloredWord B c d) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

@[simp] theorem coloredPolynomialMap_monomial (B : ℕ) (c : Fin B → Fin 3)
    (d : Fin B →₀ ℕ) (a : ℂ) :
    coloredPolynomialMap B c (monomial d a) = a • coloredWord B c d :=
  Finsupp.linearCombination_single ℂ a d

@[simp] theorem coloredPolynomialMap_product (B : ℕ) (c : Fin B → Fin 3)
    (a : Fin B → ℕ) :
    coloredPolynomialMap B c (∏ i : Fin B, (X i : MvPolynomial (Fin B) ℂ) ^ a i) =
      coloredWord B c a := by
  rw [MvPolynomial.prod_X_pow, coloredPolynomialMap_monomial, one_smul]
  congr 1
  funext i
  simp

/-- Simultaneously permuting the colored slots changes the exterior sign. -/
theorem coloredWord_perm (B : ℕ) (c : Fin B → Fin 3) (a : Fin B → ℕ)
    (e : Equiv.Perm (Fin B)) :
    coloredWord B (c ∘ e) (a ∘ e) = e.sign • coloredWord B c a :=
  (ExteriorAlgebra.ιMulti ℂ B).map_perm (fun i => currentBasis (a i, c i)) e

/-- The actual coefficient operator shifts each colored slot in turn. -/
theorem coefficientPower_coloredWord (m B : ℕ) (c : Fin B → Fin 3)
    (a : Fin B → ℕ) :
    Modules.coefficientPower m (coloredWord B c a) =
      ∑ i : Fin B, coloredWord B c (Function.update a i (a i + m)) := by
  rw [coloredWord, Modules.coefficientPower, TopAlternants.derivExt_ιMulti]
  apply Finset.sum_congr rfl
  intro i _
  unfold coloredWord
  congr 1
  funext j
  by_cases hij : j = i
  · subst j
    simp [TopAlternants.coefficientShift_currentBasis, Nat.add_comm, pow_add]
  · simp [Function.update_of_ne hij]

/-- Power sums intertwine with the already defined coefficient action. -/
theorem coloredPolynomialMap_powerSum (m B : ℕ) (c : Fin B → Fin 3)
    (p : MvPolynomial (Fin B) ℂ) :
    coloredPolynomialMap B c (psum (Fin B) ℂ m * p) =
      Modules.coefficientPower m (coloredPolynomialMap B c p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    simp only [psum, Finset.sum_mul, map_sum, X_pow_eq_monomial, monomial_mul,
      one_mul, coloredPolynomialMap_monomial, map_smul, coefficientPower_coloredWord,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    congr 1
    funext j
    by_cases hij : j = i
    · subst j
      simp [Nat.add_comm]
    · simp [hij, Ne.symm hij, Function.update_of_ne hij]
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]

/-- Every degree-B coefficient exterior basis monomial is a colored ordered word. -/
theorem coefficient_basis_eq_coloredWord (B : ℕ) (s : Finset Idx) (hs : s.card = B) :
    ∃ (c : Fin B → Fin 3) (a : Fin B → ℕ),
      coefficientRootBasis.ExteriorAlgebra s = coloredWord B c a := by
  let e : Fin B ↪o Idx := s.orderEmbOfFin hs
  refine ⟨fun i => (ofLex (e i)).2, fun i => (ofLex (e i)).1, ?_⟩
  rw [ExteriorAlgebra.basis_apply_ofCard coefficientRootBasis hs]
  change ExteriorAlgebra.ιMulti ℂ B (fun i => coefficientRootBasis (e i)) = _
  unfold coloredWord
  congr 1
  funext i
  rw [coefficientRootBasis_apply]

/-- A degree-B coefficient vector lies in every subspace containing all colored words. -/
theorem coefficient_degree_le_of_coloredWord (B : ℕ) (W : Submodule ℂ NB)
    (hW : ∀ (c : Fin B → Fin 3) (a : Fin B → ℕ), coloredWord B c a ∈ W)
    (ν : NB) (hν : LieChains.derivExt (1 : Module.End ℂ Cur) ν = (B : ℂ) • ν) :
    ν ∈ W := by
  classical
  let b := coefficientRootBasis.ExteriorAlgebra
  rw [← b.linearCombination_repr ν, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro s hs
  apply W.smul_mem
  have hc : (s.card : ℂ) = (B : ℂ) :=
    (b.apply_eq_smul_iff_of_diagonal (LieChains.derivExt (1 : Module.End ℂ Cur))
      (fun s => (s.card : ℂ)) (LieChains.derivExt_one_basis coefficientRootBasis)
      (B : ℂ) ν).mp hν s (Finsupp.mem_support_iff.mp hs)
  have hc' : s.card = B := by exact_mod_cast hc
  obtain ⟨c, a, ha⟩ := coefficient_basis_eq_coloredWord B s hc'
  rw [show b s = coloredWord B c a from ha]
  exact hW c a

end KhanSL2.PolynomialBGG
