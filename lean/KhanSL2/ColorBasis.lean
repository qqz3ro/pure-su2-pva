module

public import KhanSL2.CurrentAlgebra
public import KhanSL2.CE
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# The color coordinates are the actual matrix Lie algebra

The generators used in the finite CE formulas are normalized by
`[t_a,t_b] = epsilon a b c t_c`.  Here this normalization and its invariant
pairing are proved directly for traceless two-by-two complex matrices.
-/

noncomputable section
open scoped BigOperators Matrix

namespace KhanSL2.MatrixSL2

@[simp] theorem val_smul (r : ℂ) (m : MatrixSL2) :
    (r • m).val = r • m.val := rfl

@[simp] theorem val_add (m n : MatrixSL2) :
    (m + n).val = m.val + n.val := rfl

@[simp] theorem val_sub (m n : MatrixSL2) :
    (m - n).val = m.val - n.val := rfl

@[simp] theorem val_bracket (m n : MatrixSL2) :
    (⁅m, n⁆).val = m.val * n.val - n.val * m.val := rfl

/-- Coordinates inverse to the three epsilon-normalized color matrices. -/
def colorCoordinates (m : MatrixSL2) : Fin 3 → ℂ :=
  ![Complex.I * (m.val 0 1 + m.val 1 0),
    m.val 1 0 - m.val 0 1,
    2 * Complex.I * m.val 0 0]

/-- The color basis gives an explicit linear equivalence with `ℂ³`. -/
def colorEquiv : (Fin 3 → ℂ) ≃ₗ[ℂ] MatrixSL2 where
  toFun v := v 0 • color 0 + v 1 • color 1 + v 2 • color 2
  map_add' v w := by simp only [Pi.add_apply]; module
  map_smul' r v := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; module
  invFun := colorCoordinates
  left_inv v := by
    ext i
    fin_cases i <;>
      simp [colorCoordinates, color, h, e, f, Complex.I_mul_I] <;>
      ring_nf <;> simp [Complex.I_sq]
  right_inv m := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [colorCoordinates, color, h, e, f, diagonal, Complex.I_mul_I] <;>
      ring_nf <;> simp [Complex.I_sq] <;> ring

theorem colorEquiv_apply (v : Fin 3 → ℂ) :
    colorEquiv v = ∑ a : Fin 3, v a • color a := by
  simp [colorEquiv, Fin.sum_univ_three]

theorem color_decomposition (m : MatrixSL2) :
    ∑ a : Fin 3, colorCoordinates m a • color a = m := by
  rw [← colorEquiv_apply]
  exact colorEquiv.apply_symm_apply m

set_option maxHeartbeats 1000000 in
/-- Exactly the structure constants used by the CE differential. -/
theorem color_bracket (a b : Fin 3) :
    ⁅color a, color b⁆ = ∑ c : Fin 3, epsilon a b c • color c := by
  apply Subtype.ext
  change (color a).val * (color b).val - (color b).val * (color a).val =
    (∑ c : Fin 3, epsilon a b c • color c).val
  ext i j
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    norm_num [color, h, e, f, epsilon, LieAlgebra.SpecialLinear.sl_bracket,
      Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three,
      Complex.I_mul_I, Complex.I_sq] <;> ring_nf <;> norm_num [Complex.I_sq]

/-- The normalized invariant bilinear form used for the `bc` contraction. -/
def normalizedPairing (m n : MatrixSL2) : ℂ :=
  -2 * Matrix.trace (m.val * n.val)

theorem normalizedPairing_symmetric (m n : MatrixSL2) :
    normalizedPairing m n = normalizedPairing n m := by
  unfold normalizedPairing
  rw [Matrix.trace_mul_comm]

theorem normalizedPairing_invariant (a b c : MatrixSL2) :
    normalizedPairing ⁅a, b⁆ c = normalizedPairing a ⁅b, c⁆ := by
  have hc : Matrix.trace (b.val * a.val * c.val) =
      Matrix.trace (a.val * (c.val * b.val)) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  simp only [normalizedPairing, val_bracket, sub_mul, mul_sub, Matrix.trace_sub]
  rw [Matrix.mul_assoc a.val b.val c.val, hc]

theorem normalizedPairing_color (a b : Fin 3) :
    normalizedPairing (color a) (color b) = if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [normalizedPairing, color, h, e, f, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I, Complex.I_sq,
      Fin.ext_iff] <;> ring_nf <;> norm_num [Complex.I_sq]

end KhanSL2.MatrixSL2
