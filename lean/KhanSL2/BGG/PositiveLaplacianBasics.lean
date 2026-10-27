module

public import KhanSL2.BGG.PositiveBoundaryAdjoint

@[expose] public section

/-! The concrete algebraic Laplacian of the positive-current CE complex. -/

noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior

namespace KhanSL2.BGG.PositiveCE

/-- The anticommutator of the actual cohomology and homology differentials. -/
def laplacian : Module.End ℂ Cochain := d.comp boundary + boundary.comp d

@[simp] theorem laplacian_apply (u : Cochain) :
    laplacian u = d (boundary u) + boundary (d u) := rfl

@[simp] theorem laplacian_one : laplacian 1 = 0 := by
  rw [laplacian_apply, boundary_one, map_zero, d_one, map_zero, add_zero]

theorem laplacian_d (u : Cochain) : laplacian (d u) = d (laplacian u) := by
  simp only [laplacian_apply, d_square_zero, map_zero, add_zero, map_add, zero_add]

theorem laplacian_boundary (u : Cochain) :
    laplacian (boundary u) = boundary (laplacian u) := by
  simp only [laplacian_apply, boundary_square_zero, map_zero, zero_add, map_add, add_zero]

/-- The Laplacian is symmetric for the algebraic coefficient pairing. -/
theorem laplacian_pairing (u v : Cochain) :
    coefficientPairing (laplacian u) v = coefficientPairing u (laplacian v) := by
  have hd (x y : Cochain) : coefficientPairing (d x) y = coefficientPairing x (boundary y) := by
    rw [coefficientPairing_symm, ← boundary_pairing, coefficientPairing_symm]
  simp only [laplacian_apply, map_add, LinearMap.add_apply, hd, boundary_pairing]

/-- The actual cochain differential reverses parity. -/
theorem d_parity (u : Cochain) : d (parityLinear u) = -parityLinear (d u) := by
  apply inclusion_injective
  rw [inclusion_d, inclusion_parity, KhanSL2.q_parity]
  simp only [map_neg, inclusion_parity, inclusion_d]

/-- Contraction reverses parity. -/
theorem contract_parity (m : Mode) (u : Cochain) :
    contract m (parityLinear u) = -parityLinear (contract m u) := by
  induction u using FiniteExterior.induction_on Mode.code with
  | hzero => simp
  | hone => simp [one_def]
  | hadd u v hu hv => simp only [map_add, hu, hv, neg_add]
  | hsmul r u hu => simp only [map_smul, hu, smul_neg]
  | hgen n u hu =>
    change contract m (parityLinear (FiniteExterior.generator n * u)) =
      -parityLinear (contract m (FiniteExterior.generator n * u))
    have hp (v : Cochain) : parityLinear (FiniteExterior.generator n * v) =
        -(FiniteExterior.generator n * parityLinear v) :=
      parity_generator_wedge Mode.code n v
    rw [hp, map_neg]
    have hc (v : Cochain) : contract m (FiniteExterior.generator n * v) =
        (if m = n then v else 0) - FiniteExterior.generator n * contract m v :=
      contraction_generator_wedge Mode.code Mode.code_injective m n v
    rw [hc, hc, map_sub, hp, hu]
    split_ifs <;> simp

private theorem epsilon_boundary_contraction (k : Fin 3) (N i j : ℕ)
    (h : i + j + 1 = N) :
    (∑ b : Fin 3, ∑ c : Fin 3, epsilon k b c •
      (∑ a : Fin 3, epsilon a b c •
        FiniteExterior.generator (mergeMode (⟨i,b⟩ : Mode) (⟨j,c⟩ : Mode) a))) =
      (2 : ℂ) • FiniteExterior.generator (⟨N,k⟩ : Mode) := by
  fin_cases k <;> simp [Fin.sum_univ_succ, epsilon, mergeMode, h] <;> module

/-- A positive mode of physical energy n+1 has Laplacian eigenvalue n. -/
@[simp] theorem laplacian_generator (m : Mode) :
    laplacian (FiniteExterior.generator m) = (m.index : ℂ) • FiniteExterior.generator m := by
  rw [laplacian_apply, boundary_generator, map_zero, zero_add, d_generator]
  simp only [map_smul, map_sum, boundary_pair, smul_neg, Finset.sum_neg_distrib]
  have hterm (i : ℕ) (hi : i ∈ Finset.range m.index) :
      (∑ b : Fin 3, ∑ c : Fin 3, epsilon m.color b c •
        (∑ a : Fin 3, epsilon a b c •
          FiniteExterior.generator (mergeMode (⟨i,b⟩ : Mode)
            (⟨m.index - 1 - i,c⟩ : Mode) a))) =
        (2 : ℂ) • FiniteExterior.generator m := by
    have hi' := Finset.mem_range.mp hi
    simpa only using epsilon_boundary_contraction m.color m.index i
      (m.index - 1 - i) (by omega)
  simp_rw [neg_smul, neg_neg]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, Finset.card_range]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
  congr 1
  ring

end KhanSL2.BGG.PositiveCE
