module

public import KhanSL2.Basic
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The actual current Lie algebra

`CoefficientAlgebra` is the normal-form algebra `ℂ[x] ⊕ y ℂ[x]`,
with `y² = 0`. The variable `y` is even. Its multiplication is precisely
that of `ℂ[x,y]/(y²)`.

`CurrentLie` is the scalar extension of the traceless two-by-two matrix
Lie algebra. `constantSubalgebra` is the constant copy of sl₂.
-/

noncomputable section
open scoped TensorProduct Matrix

namespace KhanSL2

abbrev MatrixSL2 := LieAlgebra.SpecialLinear.sl (Fin 2) ℂ

abbrev CoefficientAlgebra := TrivSqZeroExt (Polynomial ℂ) (Polynomial ℂ)

def coordinateX : CoefficientAlgebra := TrivSqZeroExt.inl Polynomial.X
def coordinateY : CoefficientAlgebra := TrivSqZeroExt.inr 1

theorem coordinateY_sq : coordinateY * coordinateY = 0 := by
  exact TrivSqZeroExt.inr_mul_inr _ _ _

abbrev CurrentLie :=
  RestrictScalars ℂ CoefficientAlgebra (CoefficientAlgebra ⊗[ℂ] MatrixSL2)

def constantEmbedding : MatrixSL2 →ₗ⁅ℂ⁆ CurrentLie where
  toFun u := (1 : CoefficientAlgebra) ⊗ₜ[ℂ] u
  map_add' u v := TensorProduct.tmul_add _ _ _
  map_smul' c u := by
    change (1 : CoefficientAlgebra) ⊗ₜ[ℂ] (c • u) =
      ((algebraMap ℂ CoefficientAlgebra c) * 1) ⊗ₜ[ℂ] u
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    rw [mul_one, Algebra.algebraMap_eq_smul_one]
  map_lie' := by
    intro u v
    change (1 : CoefficientAlgebra) ⊗ₜ[ℂ] _ = (1 * 1 : CoefficientAlgebra) ⊗ₜ[ℂ] _
    simp

def constantSubalgebra : LieSubalgebra ℂ CurrentLie :=
  constantEmbedding.range

namespace MatrixSL2

def h : MatrixSL2 :=
  ⟨!![1, 0; 0, -1], by
    change Matrix.trace (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℂ) = 0
    simp [Matrix.trace_fin_two]⟩

def e : MatrixSL2 :=
  ⟨!![0, 1; 0, 0], by
    change Matrix.trace (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 0
    simp [Matrix.trace_fin_two]⟩

def f : MatrixSL2 :=
  ⟨!![0, 0; 1, 0], by
    change Matrix.trace (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) = 0
    simp [Matrix.trace_fin_two]⟩

/-- The epsilon-normalized color basis `-i σ_a / 2`. -/
def color (a : Fin 3) : MatrixSL2 :=
  ![(-Complex.I / 2) • (e + f), (1 / 2 : ℂ) • (f - e),
    (-Complex.I / 2) • h] a

theorem diagonal (m : MatrixSL2) : m.val 1 1 = -m.val 0 0 := by
  have hm : Matrix.trace m.val = 0 := m.property
  rw [Matrix.trace_fin_two] at hm
  exact eq_neg_of_add_eq_zero_right hm

theorem decompose (m : MatrixSL2) :
    m = m.val 0 0 • h + m.val 0 1 • e + m.val 1 0 • f := by
  apply Subtype.ext
  change m.val = m.val 0 0 • h.val + m.val 0 1 • e.val + m.val 1 0 • f.val
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h, e, f, diagonal]

end MatrixSL2

end KhanSL2
