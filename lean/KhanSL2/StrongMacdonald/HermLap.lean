module

public import KhanSL2.StrongMacdonald.HermPairs

@[expose] public section

/-!
# Adjointness of `∂̄`, `∂̄†` and positivity of the Laplacian

* `∂̄ = Σ_{a,m} ψ^a(-m) T_a(m)` as a locally finite sum, hence `∂̄† = dbarDag` is its adjoint.
* `X_a(m)† = Xd`, `d_a(-m)† = dUd`, and the constant action `Y_c` is skew-adjoint.
* `⟨□̄ x, x⟩ = ‖∂̄ x‖² + ‖∂̄† x‖²`, `⟨□ x, x⟩ = Σ (1/m) ‖X x‖²`, `⟨D x, x⟩ = Σ ‖d† x‖²`.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace KhanSL2.StrongMacdonald

theorem isDer_lmul_psi_mul {T : Module.End ℂ W} (hT : HomDer 0 T) (n : PMode) :
    IsDer 1 (lmul (psi n) * T) := by
  intro x y
  simp only [Module.End.mul_apply, lmul_apply]
  rw [show T (x * y) = T x * y + x * T y from hT.isDer x y]
  rw [mul_add, ← mul_assoc, ← mul_assoc, (isPar_psi n).mul_comm' x]
  simp only [mul_assoc]

theorem kills_T (a : Fin 3) : Kills (fun i => T i a) :=
  (kills_Rlow a).add ((kills_adLow a).smul fun _ => (1 / 2 : ℂ))

/-- The family `Σ_a ψ^a(-m) T_a(m)`. -/
def dbarFam (i : ℕ) : Module.End ℂ W := ∑ a, lmul (psiOf i a) * T i a

theorem kills_dbarFam : Kills dbarFam :=
  Kills.sum Finset.univ fun a _ => (kills_T a).mul_left fun i => lmul (psiOf i a)

theorem dbar_eq_lsum : dbar = lsum dbarFam kills_dbarFam.evZero := by
  apply homDer_dbar.isDer.ext (IsDer.lsum _ fun i =>
    IsDer.sum _ _ fun a _ => isDer_lmul_psi_mul (homDer_T i a) _)
  intro g
  cases g with
  | s g =>
    obtain ⟨k, b⟩ := g
    show dbar (sigOf k b) = lsum dbarFam kills_dbarFam.evZero (sigOf k b)
    rw [lsum_apply_of_bound _ k (fun i hi => by
      simp [dbarFam, T, show ¬ (i + 1 ≤ k) by omega])]
    simp only [dbar_sigOf, dbarFam, LinearMap.sum_apply, Module.End.mul_apply, lmul_apply, T,
      LinearMap.add_apply, LinearMap.smul_apply, Rlow_sigOf, adLow_sigOf, smul_zero, add_zero]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a _ => ?_
    have hi' := Finset.mem_range.mp hi
    rw [if_pos (by omega), Finset.mul_sum, show k - (i + 1) = k - 1 - i by omega]
    simp only [mul_smul_comm]
  | p n =>
    obtain ⟨k, b⟩ := n
    show dbar (psiOf k b) = lsum dbarFam kills_dbarFam.evZero (psiOf k b)
    rw [lsum_apply_of_bound _ k (fun i hi => by
      simp [dbarFam, T, show ¬ (i + 1 ≤ k) by omega])]
    simp only [dbar_psiOf, dbarFam, LinearMap.sum_apply, Module.End.mul_apply, lmul_apply, T,
      LinearMap.add_apply, LinearMap.smul_apply, Rlow_psiOf, adLow_psiOf, zero_add,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun a _ => ?_
    have hi' := Finset.mem_range.mp hi
    rw [if_pos (by omega), Finset.smul_sum, Finset.mul_sum, show k - (i + 1) = k - 1 - i by omega]
    simp only [mul_smul_comm, smul_smul, mul_comm]

/-! ## Adjoint pairs -/

theorem conj_half : conj (1 / 2 : ℂ) = 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]

theorem isAdj_T (i : ℕ) (a : Fin 3) : IsAdj (T i a) (Td i a) := by
  unfold T Td
  have h := (isAdj_Rlow a (i + 1)).add ((isAdj_adLow a (i + 1)).smul (1 / 2 : ℂ))
  rwa [conj_half] at h

theorem isAdj_X (i : ℕ) (a : Fin 3) : IsAdj (X i a) (Xd i a) := by
  unfold X Xd
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_add_eq_sub, ← sub_eq_add_neg]
  have := (isAdj_Rlow a (i + 1)).sub (isAdj_adUpDag a (i + 1))
  rw [sub_eq_add_neg, sub_eq_add_neg] at this ⊢
  convert this using 1
  abel

theorem isAdj_Xd (i : ℕ) (a : Fin 3) : IsAdj (Xd i a) (X i a) := (isAdj_X i a).symm

theorem isAdj_dUd (i : ℕ) (a : Fin 3) : IsAdj (dUd i a) (dU i a) := (isAdj_dUp a i).symm

theorem isAdj_dU (i : ℕ) (a : Fin 3) : IsAdj (dU i a) (dUd i a) := isAdj_dUp a i

theorem isAdj_dbar : IsAdj dbar dbarDag := by
  rw [dbar_eq_lsum, dbarDag]
  refine IsAdj.lsum _ _ fun i => IsAdj.sum _ fun a _ => ?_
  have h := (isAdj_psi ⟨i, a⟩).comp (isAdj_T i a)
  rw [mul_smul_comm] at h
  exact h

theorem isAdj_dbarDag : IsAdj dbarDag dbar := isAdj_dbar.symm

/-! ## The constant action is skew-adjoint -/

theorem Rup_zero (c : Fin 3) : Rup c 0 = Rlow c 0 := by
  apply (homDer_Rup c 0).isDer.ext (homDer_Rlow c 0).isDer
  intro g
  cases g with
  | s g =>
    obtain ⟨k, b⟩ := g
    change Rup c 0 (sigOf k b) = Rlow c 0 (sigOf k b)
    simp
  | p n =>
    obtain ⟨k, b⟩ := n
    change Rup c 0 (psiOf k b) = Rlow c 0 (psiOf k b)
    simp

theorem adLowDag_zero (c : Fin 3) : adLowDag c 0 = -adLow c 0 := by
  apply (homDer_adLowDag c 0).isDer.ext (homDer_adLow c 0).neg.isDer
  intro g
  cases g with
  | s g =>
    obtain ⟨k, b⟩ := g
    change adLowDag c 0 (sigOf k b) = -adLow c 0 (sigOf k b)
    simp
  | p n =>
    obtain ⟨k, b⟩ := n
    change adLowDag c 0 (psiOf k b) = -adLow c 0 (psiOf k b)
    simp only [adLowDag_psiOf, adLow_psiOf, Nat.zero_le, if_true, Nat.sub_zero, add_zero,
      LinearMap.neg_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    have hk : ((k : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero k
    push_cast
    rw [div_self hk, mul_one, epsilon_swap_right, neg_smul]

theorem isAdj_Y (c : Fin 3) : IsAdj (Y c) (-Y c) := by
  unfold Y
  have h := (isAdj_Rlow c 0).add (isAdj_adLow c 0)
  rw [Rup_zero, adLowDag_zero] at h
  rw [neg_add]
  exact h

/-! ## Positivity -/

theorem herm_lap_self (x : W) :
    herm (lap x) x = herm (dbar x) (dbar x) + herm (dbarDag x) (dbarDag x) := by
  rw [lap, LinearMap.add_apply, herm_add_left, Module.End.mul_apply, Module.End.mul_apply,
    isAdj_dbar (dbarDag x) x, isAdj_dbarDag (dbar x) x, add_comm]

theorem herm_isAdj_self {P Q : Module.End ℂ W} (h : IsAdj P Q) (x : W) :
    herm ((Q * P) x) x = herm (P x) (P x) := by
  rw [Module.End.mul_apply, h.symm]

end KhanSL2.StrongMacdonald
