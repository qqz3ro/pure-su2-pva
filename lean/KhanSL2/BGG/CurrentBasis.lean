module

public import KhanSL2.BGG.CurrentPositive
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.Tactic.Module

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Explicit root-mode bases for polynomial currents and positive currents. -/

noncomputable section
open scoped TensorProduct Matrix

namespace KhanSL2.BGG

/-- Root coordinates in the order `e,h,f`. -/
def rootEquiv : (Fin 3 → ℂ) ≃ₗ[ℂ] G where
  toFun v := v 0 • MatrixSL2.e + v 1 • MatrixSL2.h + v 2 • MatrixSL2.f
  invFun x := ![x.val 0 1, x.val 0 0, x.val 1 0]
  map_add' v w := by simp only [Pi.add_apply]; module
  map_smul' a v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; module
  left_inv v := by
    ext i
    fin_cases i <;> simp [MatrixSL2.e, MatrixSL2.h, MatrixSL2.f]
  right_inv x := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [MatrixSL2.e, MatrixSL2.h, MatrixSL2.f, MatrixSL2.diagonal]

def rootBasis : Module.Basis (Fin 3) ℂ G := (Pi.basisFun ℂ (Fin 3)).map rootEquiv

@[simp] theorem rootBasis_zero : rootBasis 0 = MatrixSL2.e := by
  simp [rootBasis, rootEquiv, Pi.basisFun_apply]

@[simp] theorem rootBasis_one : rootBasis 1 = MatrixSL2.h := by
  simp [rootBasis, rootEquiv, Pi.basisFun_apply]

@[simp] theorem rootBasis_two : rootBasis 2 = MatrixSL2.f := by
  simp [rootBasis, rootEquiv, Pi.basisFun_apply]

/-- The Cartan eigenvalue of a root color. -/
def rootWeight : Fin 3 → ℂ := ![2, 0, -2]

theorem lie_h_rootBasis (a : Fin 3) :
    ⁅MatrixSL2.h, rootBasis a⁆ = rootWeight a • rootBasis a := by
  fin_cases a
  · simpa [rootWeight] using G.lie_h_e
  · simp [rootWeight, LieRing.lie_self]
  · simpa [rootWeight] using G.lie_h_f
/-- The actual polynomial-current basis, indexed by mode and root color. -/
def currentBasis : Module.Basis (ℕ × Fin 3) ℂ Current :=
  (Polynomial.basisMonomials ℂ).tensorProduct rootBasis

@[simp] theorem currentBasis_apply (n : ℕ) (a : Fin 3) :
    currentBasis (n, a) = mode n (rootBasis a) := by
  simp [currentBasis, Polynomial.coe_basisMonomials,
    Polynomial.monomial_one_right_eq_X_pow]

/-- The actual constant Cartan bracket is diagonal on the current root-mode basis. -/
theorem constant_h_lie_currentBasis (n : ℕ) (a : Fin 3) :
    ⁅constant MatrixSL2.h, currentBasis (n, a)⁆ = rootWeight a • currentBasis (n, a) := by
  rw [currentBasis_apply, constant_apply, mode_lie, zero_add, lie_h_rootBasis, map_smul]
/-- The positive-mode root vectors are linearly independent. -/
theorem positiveRoot_linearIndependent :
    LinearIndependent ℂ (fun i : ℕ × Fin 3 => positiveMode i.1 (rootBasis i.2)) := by
  apply LinearIndependent.of_comp positive.toLieSubalgebra.incl.toLinearMap
  have h := currentBasis.linearIndependent.comp
    (fun i : ℕ × Fin 3 => (i.1 + 1, i.2)) (by
      intro i j h
      apply Prod.ext
      · exact Nat.add_right_cancel (congrArg (fun p : ℕ × Fin 3 => p.1) h)
      · have h2 := congrArg (fun p : ℕ × Fin 3 => p.2) h
        exact h2)
  change LinearIndependent ℂ (fun i : ℕ × Fin 3 => mode (i.1 + 1) (rootBasis i.2))
  simpa only [Function.comp_def, currentBasis_apply] using h

/-- Removing a constant leaves a linear combination of positive modes. -/
theorem sub_constant_mem_submodule (M : Submodule ℂ Current)
    (hpos : ∀ (n : ℕ) (x : G), mode (n + 1) x ∈ M) (u : Current) :
    u - constant (evalZero u) ∈ M := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv =>
    simpa only [map_add, add_sub_add_comm] using M.add_mem hu hv
  | tmul p x =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [TensorProduct.add_tmul, map_add, add_sub_add_comm] using M.add_mem hp hq
    | monomial n a =>
      rw [monomial_tmul]
      cases n with
      | zero => simp
      | succ n =>
        simpa only [evalZero_positive_mode, map_zero, sub_zero] using hpos n (a • x)

/-- The positive root modes linearly span the actual positive-current ideal. -/
theorem positiveRoot_span_eq_top :
    Submodule.span ℂ (Set.range (fun i : ℕ × Fin 3 => positiveMode i.1 (rootBasis i.2))) = ⊤ := by
  let M := Submodule.span ℂ
    (Set.range (fun i : ℕ × Fin 3 => positiveMode i.1 (rootBasis i.2)))
  have hmem (n : ℕ) (x : G) : positiveMode n x ∈ M := by
    rw [← rootBasis.sum_repr x, map_sum]
    apply M.sum_mem
    intro a _
    rw [map_smul]
    exact M.smul_mem _ (Submodule.subset_span ⟨(n, a), rfl⟩)
  let M' := M.map positive.toLieSubalgebra.incl.toLinearMap
  have hm (n : ℕ) (x : G) : mode (n + 1) x ∈ M' :=
    ⟨positiveMode n x, hmem n x, rfl⟩
  apply eq_top_iff.mpr
  intro u _
  have hu : (u : Current) ∈ M' := by
    have h := sub_constant_mem_submodule M' hm (u : Current)
    have hzero : evalZero (u : Current) = 0 := u.property
    simpa only [hzero, map_zero, sub_zero] using h
  obtain ⟨v, hv, hvu⟩ := hu
  have heq : v = u := Subtype.ext hvu
  exact heq ▸ hv

/-- The positive-current basis is `eₙ,hₙ,fₙ` for physical modes `n ≥ 1`. -/
def positiveBasis : Module.Basis (ℕ × Fin 3) ℂ positive :=
  Module.Basis.mk positiveRoot_linearIndependent (by rw [positiveRoot_span_eq_top])

@[simp] theorem positiveBasis_apply (n : ℕ) (a : Fin 3) :
    positiveBasis (n, a) = positiveMode n (rootBasis a) := by
  simp [positiveBasis]

end KhanSL2.BGG