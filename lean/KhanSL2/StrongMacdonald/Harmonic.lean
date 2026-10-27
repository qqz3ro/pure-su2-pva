module

public import KhanSL2.StrongMacdonald.Invariants

@[expose] public section

/-!
# Harmonic invariants

On invariants, `⟨□̄ x, x⟩ = Σ_{a,m} (1/m) ‖X_a(m) x‖² + Σ_{a,m} ‖d_a(-m)† x‖²` and also
`⟨□̄ x, x⟩ = ‖∂̄ x‖² + ‖∂̄† x‖²`. Hence an invariant is harmonic (killed by `∂̄` and `∂̄†`)
exactly when it lies in the joint kernel of all `X_a(m)` and all `d_a(-m)†`.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace KhanSL2.StrongMacdonald

/-- The real loop weight `1/(i+1)`. -/
def lamR (i : ℕ) : ℝ := 1 / ((i : ℝ) + 1)

theorem lamR_pos (i : ℕ) : 0 < lamR i := by
  unfold lamR
  positivity

theorem lam_eq_ofReal (i : ℕ) : lam i = (lamR i : ℂ) := by
  simp [lam, lamR]

theorem ofReal_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : ℂ) = ∑ i ∈ s, (f i : ℂ) := by
  rw [← Complex.ofRealHom_eq_coe, map_sum]
  rfl

theorem herm_boxFam (i : ℕ) (x : W) :
    herm (boxFam i x) x = ∑ a, ((lamR i * hnormSq (X i a x) : ℝ) : ℂ) := by
  simp only [boxFam, LinearMap.sum_apply, LinearMap.smul_apply, herm_sum_left, herm_smul_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [herm_isAdj_self (isAdj_X i a), herm_self, lam_eq_ofReal, Complex.conj_ofReal,
    Complex.ofReal_mul]

theorem herm_DFam (i : ℕ) (x : W) :
    herm (DFam i x) x = ∑ a, ((hnormSq (dUd i a x) : ℝ) : ℂ) := by
  simp only [DFam, LinearMap.sum_apply, herm_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [herm_isAdj_self (isAdj_dUd i a), herm_self]

/-- `⟨□̄ x, x⟩` on an invariant, as an explicit sum of squares. -/
theorem herm_lap_of_mem_inv {x : W} (hx : x ∈ inv) {N : ℕ} (hN : Low N x) :
    herm (lap x) x = ((∑ i ∈ Finset.range N, ∑ a,
      (lamR i * hnormSq (X i a x) + hnormSq (dUd i a x)) : ℝ) : ℂ) := by
  rw [lap_apply_of_mem_inv hx, herm_add_left, boxOp, DOp, lsum_apply_low kills_box hN,
    lsum_apply_low kills_D hN, herm_sum_left, herm_sum_left, ← Finset.sum_add_distrib,
    ofReal_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [herm_boxFam, herm_DFam, ← Finset.sum_add_distrib, ofReal_finsetSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_add]

theorem eq_zero_and_eq_zero_of_herm_add {x y : W} (h : herm x x + herm y y = 0) :
    x = 0 ∧ y = 0 := by
  rw [herm_self, herm_self, ← Complex.ofReal_add, Complex.ofReal_eq_zero] at h
  have hx := hnormSq_nonneg x
  have hy := hnormSq_nonneg y
  exact ⟨hnormSq_eq_zero (by linarith), hnormSq_eq_zero (by linarith)⟩

/-- Harmonic means killed by `∂̄` and `∂̄†`. -/
theorem lap_eq_zero_iff (x : W) : lap x = 0 ↔ dbar x = 0 ∧ dbarDag x = 0 := by
  constructor
  · intro h
    have h1 := herm_lap_self x
    rw [h, herm_zero_left] at h1
    exact eq_zero_and_eq_zero_of_herm_add h1.symm
  · rintro ⟨h1, h2⟩
    rw [lap, LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, h1, h2, map_zero,
      map_zero, add_zero]

/-- FGT: on invariants, harmonic = joint kernel of the `X_a(m)` and the `d_a(-m)†`. -/
theorem lap_eq_zero_iff_of_mem_inv {x : W} (hx : x ∈ inv) :
    lap x = 0 ↔ (∀ i a, X i a x = 0) ∧ (∀ i a, dUd i a x = 0) := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := exists_low x
    have h1 := herm_lap_of_mem_inv hx hN
    rw [h, herm_zero_left, eq_comm, Complex.ofReal_eq_zero] at h1
    have hterm : ∀ i ∈ Finset.range N, ∀ a,
        lamR i * hnormSq (X i a x) + hnormSq (dUd i a x) = 0 := by
      intro i hi a
      have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun a _ =>
        add_nonneg (mul_nonneg (lamR_pos i).le (hnormSq_nonneg _)) (hnormSq_nonneg _))).mp h1 i hi
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
        add_nonneg (mul_nonneg (lamR_pos i).le (hnormSq_nonneg _)) (hnormSq_nonneg _))).mp h2 a
        (Finset.mem_univ a)
    have hsplit : ∀ i ∈ Finset.range N, ∀ a, X i a x = 0 ∧ dUd i a x = 0 := by
      intro i hi a
      have h3 := hterm i hi a
      have hp := mul_nonneg (lamR_pos i).le (hnormSq_nonneg (X i a x))
      have hq := hnormSq_nonneg (dUd i a x)
      have h4 : lamR i * hnormSq (X i a x) = 0 := by linarith
      refine ⟨hnormSq_eq_zero ?_, hnormSq_eq_zero (by linarith)⟩
      exact (mul_eq_zero.mp h4).resolve_left (lamR_pos i).ne'
    refine ⟨fun i a => ?_, fun i a => ?_⟩
    · by_cases hi : i < N
      · exact (hsplit i (Finset.mem_range.mpr hi) a).1
      · exact kills_X a N i (by omega) x hN
    · by_cases hi : i < N
      · exact (hsplit i (Finset.mem_range.mpr hi) a).2
      · exact kills_dUd a N i (by omega) x hN
  · rintro ⟨hX, hD⟩
    rw [lap_apply_of_mem_inv hx, boxOp, DOp,
      lsum_apply_of _ (N := 0) fun i _ => by simp [boxFam, hX],
      lsum_apply_of _ (N := 0) fun i _ => by simp [DFam, hD]]
    simp

/-! ## The harmonic invariants -/

/-- Harmonic invariants: invariants killed by `∂̄` and `∂̄†`. -/
def harm : Submodule ℂ W := inv ⊓ LinearMap.ker dbar ⊓ LinearMap.ker dbarDag

theorem mem_harm {x : W} : x ∈ harm ↔ x ∈ inv ∧ dbar x = 0 ∧ dbarDag x = 0 := by
  simp [harm, and_assoc]

/-- FGT Theorem 3.11 consequence: the harmonic invariants are the invariants in the joint
kernel of the `X_a(m)` and `d_a(-m)†`. -/
theorem mem_harm_iff {x : W} :
    x ∈ harm ↔ x ∈ inv ∧ (∀ i a, X i a x = 0) ∧ (∀ i a, dUd i a x = 0) := by
  rw [mem_harm]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, (lap_eq_zero_iff_of_mem_inv hx).mp ((lap_eq_zero_iff x).mpr h)⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, (lap_eq_zero_iff x).mp ((lap_eq_zero_iff_of_mem_inv hx).mpr h)⟩

end KhanSL2.StrongMacdonald
