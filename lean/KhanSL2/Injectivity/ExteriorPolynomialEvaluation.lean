module

public import KhanSL2.Injectivity.ExteriorSubstitution
public import KhanSL2.Injectivity.OrderedProducts
public import KhanSL2.Injectivity.ExteriorWords
public import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Polynomial-valued evaluation of finite exterior chains. -/

@[expose] public section

noncomputable section

namespace KhanSL2.FiniteExterior

open KhanSL2.Injectivity

variable {α : Type*} [DecidableEq α] [GeneratorOrder α]
variable {P : Type*} [CommRing P] [Algebra ℂ P]

/-- A determinant over `P`, viewed as an alternating map over `ℂ`. -/
def complexDeterminant (n : ℕ) : (Fin n → P) [⋀^Fin n]→ₗ[ℂ] P where
  toMultilinearMap := (Matrix.detRowAlternating (R := P) (n := Fin n)).toMultilinearMap.restrictScalars ℂ
  map_eq_zero_of_eq' v _i _j hij hne :=
    (Matrix.detRowAlternating (R := P) (n := Fin n)).map_eq_zero_of_eq v hij hne

@[simp] theorem complexDeterminant_apply (n : ℕ) (v : Fin n → Fin n → P) :
    complexDeterminant n v = Matrix.det v := rfl

/-- The determinant in degree `n`, and zero in every other exterior degree. -/
def determinantDegree (n i : ℕ) : (Fin n → P) [⋀^Fin i]→ₗ[ℂ] P :=
  if h : i = n then by subst i; exact complexDeterminant n else 0

@[simp] theorem determinantDegree_self (n : ℕ) :
    determinantDegree (P := P) n n = complexDeterminant n := by
  simp [determinantDegree]

@[simp] theorem determinantDegree_other (n i : ℕ) (h : i ≠ n) :
    determinantDegree (P := P) n i = 0 := by
  simp [determinantDegree, h]

def determinantComponent (n : ℕ) : ExteriorAlgebra ℂ (Fin n → P) →ₗ[ℂ] P :=
  ExteriorAlgebra.liftAlternating (determinantDegree n)

@[simp] theorem determinantComponent_ιMulti (n : ℕ) (v : Fin n → Fin n → P) :
    determinantComponent n (ExteriorAlgebra.ιMulti ℂ n v) = Matrix.det v := by
  rw [determinantComponent, ExteriorAlgebra.liftAlternating_apply_ιMulti,
    determinantDegree_self, complexDeterminant_apply]

theorem determinantComponent_ιMulti_other (n i : ℕ) (v : Fin i → Fin n → P) (h : i ≠ n) :
    determinantComponent n (ExteriorAlgebra.ιMulti ℂ i v) = 0 := by
  rw [determinantComponent, ExteriorAlgebra.liftAlternating_apply_ιMulti,
    determinantDegree_other n i h]
  rfl

/-- Substitute a finite vector of polynomial weights for every mode. -/
def slotSubstitution (n : ℕ) (weights : α → Fin n → P) :
    Exterior α →ₐ[ℂ] ExteriorAlgebra ℂ (Fin n → P) :=
  substitute (fun a => ExteriorAlgebra.ι ℂ (weights a))
    (fun a => ExteriorAlgebra.ι_sq_zero (weights a))
    (fun a b => eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (weights a) (weights b)))

@[simp] theorem slotSubstitution_generator (n : ℕ) (weights : α → Fin n → P) (a : α) :
    slotSubstitution n weights (generator a) = ExteriorAlgebra.ι ℂ (weights a) :=
  substitute_generator _ _ _ a

theorem slotSubstitution_orderedProduct (n i : ℕ) (weights : α → Fin n → P) (a : Fin i → α) :
    slotSubstitution n weights (orderedProduct (fun j => generator (a j))) =
      ExteriorAlgebra.ιMulti ℂ i (fun j => weights (a j)) := by
  simp only [orderedProduct, map_list_prod, List.map_ofFn, slotSubstitution_generator,
    ExteriorAlgebra.ιMulti_apply, Function.comp_def]

/-- A completely finite polynomial-valued linear functional on chains. -/
def determinantEvaluation (n : ℕ) (weights : α → Fin n → P) : Exterior α →ₗ[ℂ] P :=
  (determinantComponent n).comp (slotSubstitution n weights).toLinearMap

theorem determinantEvaluation_orderedProduct (n : ℕ) (weights : α → Fin n → P)
    (a : Fin n → α) :
    determinantEvaluation n weights (orderedProduct (fun j => generator (a j))) =
      Matrix.det (fun i j => weights (a i) j) := by
  change determinantComponent n
    (slotSubstitution n weights (orderedProduct (fun j => generator (a j)))) = _
  rw [slotSubstitution_orderedProduct, determinantComponent_ιMulti]

theorem determinantEvaluation_orderedProduct_other (n i : ℕ) (weights : α → Fin n → P)
    (a : Fin i → α) (h : i ≠ n) :
    determinantEvaluation n weights (orderedProduct (fun j => generator (a j))) = 0 := by
  change determinantComponent n
    (slotSubstitution n weights (orderedProduct (fun j => generator (a j)))) = 0
  rw [slotSubstitution_orderedProduct, determinantComponent_ιMulti_other n i _ h]

end KhanSL2.FiniteExterior
