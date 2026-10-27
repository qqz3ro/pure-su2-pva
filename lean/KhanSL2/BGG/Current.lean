module

public import KhanSL2.CurrentAlgebra

@[expose] public section

/-! The polynomial current Lie algebra and its generators in degrees zero and one.
The bracket is scalar extension of the actual traceless-matrix commutator. -/

noncomputable section
open scoped TensorProduct Matrix

namespace KhanSL2.BGG

abbrev G := MatrixSL2
abbrev Current := Polynomial ℂ ⊗[ℂ] G

/-- A homogeneous polynomial current. -/
def mode (n : ℕ) : G →ₗ[ℂ] Current :=
  TensorProduct.mk ℂ (Polynomial ℂ) G (Polynomial.X ^ n)

@[simp] theorem mode_apply (n : ℕ) (x : G) :
    mode n x = (Polynomial.X ^ n) ⊗ₜ[ℂ] x := rfl

theorem mode_lie (i j : ℕ) (x y : G) :
    ⁅mode i x, mode j y⁆ = mode (i + j) ⁅x, y⁆ := by
  change (Polynomial.X ^ i * Polynomial.X ^ j) ⊗ₜ[ℂ] ⁅x, y⁆ =
    (Polynomial.X ^ (i + j)) ⊗ₜ[ℂ] ⁅x, y⁆
  rw [pow_add]

/-- The constant copy of sl₂ in its polynomial current algebra. -/
def constant : G →ₗ⁅ℂ⁆ Current where
  toLinearMap := mode 0
  map_lie' := by
    intro x y
    exact (mode_lie 0 0 x y).symm

@[simp] theorem constant_apply (x : G) : constant x = mode 0 x := rfl

namespace G

theorem lie_e_f : ⁅MatrixSL2.e, MatrixSL2.f⁆ = MatrixSL2.h := by
  apply Subtype.ext
  change _ * _ - _ * _ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [MatrixSL2.e, MatrixSL2.f, MatrixSL2.h,
      LieAlgebra.SpecialLinear.sl_bracket, Matrix.mul_apply, Fin.sum_univ_two]

theorem lie_h_e : ⁅MatrixSL2.h, MatrixSL2.e⁆ = (2 : ℂ) • MatrixSL2.e := by
  apply Subtype.ext
  change _ * _ - _ * _ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [MatrixSL2.e, MatrixSL2.h,
      LieAlgebra.SpecialLinear.sl_bracket, Matrix.mul_apply, Fin.sum_univ_two]

theorem lie_h_f : ⁅MatrixSL2.h, MatrixSL2.f⁆ = (-2 : ℂ) • MatrixSL2.f := by
  apply Subtype.ext
  change _ * _ - _ * _ = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [MatrixSL2.f, MatrixSL2.h,
      LieAlgebra.SpecialLinear.sl_bracket, Matrix.mul_apply, Fin.sum_univ_two]

end G

/-- Bracketing degree-one currents with degree-`n` currents generates the
entire next homogeneous piece. -/
theorem mode_succ_mem (K : LieSubalgebra ℂ Current) (n : ℕ)
    (h1 : ∀ x : G, mode 1 x ∈ K) (hn : ∀ x : G, mode n x ∈ K) :
    ∀ x : G, mode (n + 1) x ∈ K := by
  have hh : mode (n + 1) MatrixSL2.h ∈ K := by
    simpa only [mode_lie, Nat.one_add, G.lie_e_f] using
      K.lie_mem (h1 MatrixSL2.e) (hn MatrixSL2.f)
  have he2 : mode (n + 1) ((2 : ℂ) • MatrixSL2.e) ∈ K := by
    simpa only [mode_lie, Nat.one_add, G.lie_h_e] using
      K.lie_mem (h1 MatrixSL2.h) (hn MatrixSL2.e)
  have hf2 : mode (n + 1) ((-2 : ℂ) • MatrixSL2.f) ∈ K := by
    simpa only [mode_lie, Nat.one_add, G.lie_h_f] using
      K.lie_mem (h1 MatrixSL2.h) (hn MatrixSL2.f)
  have he : mode (n + 1) MatrixSL2.e ∈ K := by
    rw [map_smul] at he2
    simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
      using K.smul_mem ((2 : ℂ)⁻¹) he2
  have hf : mode (n + 1) MatrixSL2.f ∈ K := by
    rw [map_smul] at hf2
    simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (-2 : ℂ) ≠ 0), one_smul]
      using K.smul_mem ((-2 : ℂ)⁻¹) hf2
  intro x
  rw [MatrixSL2.decompose x, map_add, map_add, map_smul, map_smul, map_smul]
  exact K.add_mem (K.add_mem (K.smul_mem _ hh) (K.smul_mem _ he)) (K.smul_mem _ hf)

theorem positive_modes_mem (K : LieSubalgebra ℂ Current)
    (h1 : ∀ x : G, mode 1 x ∈ K) (n : ℕ) : ∀ x : G, mode (n + 1) x ∈ K := by
  induction n with
  | zero => exact h1
  | succ n ih => exact mode_succ_mem K (n + 1) h1 ih

/-- The homogeneous currents span the whole polynomial current vector space. -/
theorem eq_top_of_all_modes (K : LieSubalgebra ℂ Current)
    (hm : ∀ n (x : G), mode n x ∈ K) : K = ⊤ := by
  have hall : ∀ u : Current, u ∈ K := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact K.zero_mem
    | add u v hu hv => exact K.add_mem hu hv
    | tmul p x =>
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
        rw [TensorProduct.add_tmul]
        exact K.add_mem hp hq
      | monomial n a =>
        have h := K.smul_mem a (hm n x)
        have heq : a • mode n x = (Polynomial.monomial n a) ⊗ₜ[ℂ] x := by
          change a • ((Polynomial.X ^ n) ⊗ₜ[ℂ] x) = _
          rw [TensorProduct.smul_tmul', Polynomial.smul_X_eq_monomial]
        exact heq ▸ h
  exact eq_top_iff.mpr (fun u _ => hall u)
/-- Constants and currents of mode degree one generate all polynomial currents. -/
theorem eq_top_of_modes (K : LieSubalgebra ℂ Current)
    (h0 : ∀ x : G, mode 0 x ∈ K) (h1 : ∀ x : G, mode 1 x ∈ K) : K = ⊤ := by
  apply eq_top_of_all_modes K
  intro n x
  cases n with
  | zero => exact h0 x
  | succ n => exact positive_modes_mem K h1 n x

theorem lieSpan_modes_eq_top :
    LieSubalgebra.lieSpan ℂ Current (Set.range (mode 0) ∪ Set.range (mode 1)) = ⊤ := by
  apply eq_top_of_modes
  · intro x
    exact LieSubalgebra.subset_lieSpan (Or.inl (Set.mem_range_self x))
  · intro x
    exact LieSubalgebra.subset_lieSpan (Or.inr (Set.mem_range_self x))

end KhanSL2.BGG