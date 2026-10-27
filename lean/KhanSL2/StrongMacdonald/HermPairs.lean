module

public import KhanSL2.StrongMacdonald.HermDer

@[expose] public section

/-!
# The adjoint pairs of the FGT operators

`R_a(m)† = -R_a(-m)`, `ad_a(m)† = adLowDag`, `ad_a(-m)† = adUpDag`, `d_a(-m)† = dUpDag`.
Each is obtained from the elementary representation of one side; the other side is identified
by derivation extensionality.
-/

noncomputable section
open scoped BigOperators ComplexConjugate

namespace KhanSL2.StrongMacdonald

open AddMonoidAlgebra (single)

@[simp] theorem dS_sigOf (k j : ℕ) (b c : Fin 3) :
    dS ⟨k, b⟩ (sigOf j c) = if k = j ∧ b = c then 1 else 0 := by
  rw [sigOf, dS_sig]
  simp only [SMode.mk.injEq]

@[simp] theorem dS_psiOf (k j : ℕ) (b c : Fin 3) : dS ⟨k, b⟩ (psiOf j c) = 0 := by
  rw [psiOf, dS_psi]

@[simp] theorem iP_psiOf (k j : ℕ) (b c : Fin 3) :
    iP ⟨k, b⟩ (psiOf j c) = if k = j ∧ b = c then 1 else 0 := by
  rw [psiOf, iP_psi]
  congr 1
  apply propext
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem iP_sigOf (k j : ℕ) (b c : Fin 3) : iP ⟨k, b⟩ (sigOf j c) = 0 := by
  rw [sigOf, iP_sig]

/-- Evaluating a locally finite sum of `adjFam` on a generator of index `j`: only the indices
`< N` matter for any `N` beyond the relevant range. -/
theorem lsum_apply_of_bound {P : ℕ → Module.End ℂ W} (hP : EvZero P) {x : W} (N : ℕ)
    (hN : ∀ i, N ≤ i → P i x = 0) : lsum P hP x = ∑ i ∈ Finset.range N, P i x :=
  lsum_apply_of hP hN

theorem sum_range_ite_add_eq {M : Type*} [AddCommMonoid M] (N m j : ℕ) (hN : j < N + m)
    (F : ℕ → M) :
    ∑ k ∈ Finset.range N, (if k + m = j then F k else 0) =
      if m ≤ j then F (j - m) else 0 := by
  rw [Finset.sum_ite]
  by_cases hmj : m ≤ j
  · rw [if_pos hmj]
    have : Finset.filter (fun k => k + m = j) (Finset.range N) = {j - m} := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
    rw [this]; simp
  · rw [if_neg hmj]
    have : Finset.filter (fun k => k + m = j) (Finset.range N) = ∅ := by
      ext k; simp only [Finset.mem_filter, Finset.mem_range]; simp; omega
    rw [this]; simp

theorem sum_range_ite_sub_eq {M : Type*} [AddCommMonoid M] (N m j : ℕ) (hN : j + m < N)
    (F : ℕ → M) :
    ∑ k ∈ Finset.range N, (if m ≤ k ∧ k - m = j then F k else 0) = F (j + m) := by
  rw [Finset.sum_ite]
  have : Finset.filter (fun k => m ≤ k ∧ k - m = j) (Finset.range N) = {j + m} := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
  rw [this]; simp

/-! ## `R_a(-m)† = -R_a(m)` -/

/-- The adjoint of multiplication by `R_a(-m) σ(k, b)`. -/
def YRup (a : Fin 3) (m k : ℕ) (b : Fin 3) : Module.End ℂ W :=
  ∑ c, epsilon a b c • dS ⟨k + m, c⟩

theorem evZero_adjFam_Rup (a : Fin 3) (m : ℕ) :
    EvZero (adjFam (fun k b => YRup a m k b) (fun _ _ => 0)) := by
  intro x
  obtain ⟨N, hx⟩ := exists_low x
  refine ⟨N, fun k hk => ?_⟩
  simp only [adjFam, YRup, mul_zero, smul_zero, add_zero, LinearMap.sum_apply,
    Module.End.mul_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
  rw [(kills_dS c) N (k + m) (by omega) x hx]
  simp

theorem isDer_adjFam_Rup (a : Fin 3) (m k : ℕ) :
    IsDer 0 (adjFam (fun k b => YRup a m k b) (fun _ _ => 0) k) := by
  unfold adjFam YRup
  simp only [mul_zero, smul_zero, add_zero, Finset.mul_sum, mul_smul_comm]
  exact IsDer.sum _ _ fun b _ => IsDer.sum _ _ fun c _ =>
    (isDer_lmul_dS (isPar_sigOf k b) _).smul _

theorem adjFam_Rup_sigOf (a : Fin 3) (m k j : ℕ) (c' : Fin 3) :
    adjFam (fun k b => YRup a m k b) (fun _ _ => 0) k (sigOf j c') =
      if k + m = j then ∑ b, epsilon a b c' • sigOf k b else 0 := by
  simp only [adjFam, YRup, mul_zero, smul_zero, add_zero, LinearMap.sum_apply,
    Module.End.mul_apply, LinearMap.smul_apply, map_sum, map_smul, lmul_apply, dS_sigOf,
    ite_and, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp [Finset.mul_sum]

theorem adjFam_Rup_psiOf (a : Fin 3) (m k j : ℕ) (c' : Fin 3) :
    adjFam (fun k b => YRup a m k b) (fun _ _ => 0) k (psiOf j c') = 0 := by
  simp [adjFam, YRup]

theorem adjFam_Rup_eq (a : Fin 3) (m : ℕ) :
    lsum _ (evZero_adjFam_Rup a m) = -Rlow a m := by
  symm
  apply (homDer_Rlow a m).neg.isDer.ext (IsDer.lsum _ (isDer_adjFam_Rup a m))
  intro g
  cases g with
  | s g =>
    obtain ⟨j, c'⟩ := g
    change -Rlow a m (sigOf j c') = lsum _ _ (sigOf j c')
    rw [lsum_apply_of_bound _ (j + 1) (fun i hi => by
      rw [adjFam_Rup_sigOf, if_neg (by omega)])]
    simp only [adjFam_Rup_sigOf]
    rw [sum_range_ite_add_eq _ _ _ (by omega), Rlow_sigOf]
    split
    · rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [epsilon_swap_right, neg_smul, neg_neg]
    · simp
  | p n =>
    obtain ⟨j, c'⟩ := n
    change -Rlow a m (psiOf j c') = lsum _ _ (psiOf j c')
    rw [lsum_apply_of_bound _ 0 (fun i _ => adjFam_Rup_psiOf a m i j c')]
    simp

/-- `R_a(-m)† = -R_a(m)`. -/
theorem isAdj_Rup (a : Fin 3) (m : ℕ) : IsAdj (Rup a m) (-Rlow a m) := by
  rw [← adjFam_Rup_eq]
  apply isAdj_of_rep (homDer_Rup a m)
  · intro k b
    rw [Rup_sigOf]
    have := isAdj_lmul_sigs Finset.univ (fun c => epsilon a b c) (fun _ => k + m)
    simp only [conj_epsilon] at this
    exact this
  · intro k b
    rw [Rup_psiOf, lmul_zero]
    exact IsAdj.zero

/-- `R_a(m)† = -R_a(-m)`. -/
theorem isAdj_Rlow (a : Fin 3) (m : ℕ) : IsAdj (Rlow a m) (-Rup a m) := by
  have := (isAdj_Rup a m).symm.neg
  rwa [neg_neg] at this

/-! ## `ad_a(-m)† = adUpDag` -/

def YadUp (a : Fin 3) (m k : ℕ) (b : Fin 3) : Module.End ℂ W :=
  ∑ c, (epsilon a b c * lamP ⟨k + m, c⟩) • iP ⟨k + m, c⟩

theorem evZero_adjFam_adUp (a : Fin 3) (m : ℕ) :
    EvZero (adjFam (fun _ _ => 0) (fun k b => YadUp a m k b)) := by
  intro x
  obtain ⟨N, hx⟩ := exists_low x
  refine ⟨N, fun k hk => ?_⟩
  have h0 : ∀ c, iP ⟨k + m, c⟩ x = 0 := fun c => (kills_iP c) N (k + m) (by omega) x hx
  simp [adjFam, YadUp, h0]

theorem isDer_adjFam_adUp (a : Fin 3) (m k : ℕ) :
    IsDer 0 (adjFam (fun _ _ => 0) (fun k b => YadUp a m k b) k) := by
  unfold adjFam YadUp
  simp only [mul_zero, zero_add, Finset.mul_sum, mul_smul_comm]
  exact IsDer.sum _ _ fun b _ => (IsDer.sum _ _ fun c _ =>
    (isDer_lmul_iP (isPar_psiOf k b) _).smul _).smul _

theorem adjFam_adUp_psiOf (a : Fin 3) (m k j : ℕ) (c' : Fin 3) :
    adjFam (fun _ _ => 0) (fun k b => YadUp a m k b) k (psiOf j c') =
      if k + m = j then
        ∑ b, (((k : ℂ) + 1) * (epsilon a b c' * lamP ⟨j, c'⟩)) • psiOf k b else 0 := by
  simp only [adjFam, YadUp, mul_zero, zero_add, LinearMap.sum_apply,
    Module.End.mul_apply, LinearMap.smul_apply, map_sum, map_smul, lmul_apply, iP_psiOf,
    ite_and, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs with h
  · subst h
    simp [Finset.mul_sum, smul_smul, mul_comm]
  · simp

theorem adjFam_adUp_sigOf (a : Fin 3) (m k j : ℕ) (c' : Fin 3) :
    adjFam (fun _ _ => 0) (fun k b => YadUp a m k b) k (sigOf j c') = 0 := by
  simp [adjFam, YadUp]

theorem adjFam_adUp_eq (a : Fin 3) (m : ℕ) :
    lsum _ (evZero_adjFam_adUp a m) = adUpDag a m := by
  symm
  apply (homDer_adUpDag a m).isDer.ext (IsDer.lsum _ (isDer_adjFam_adUp a m))
  intro g
  cases g with
  | s g =>
    obtain ⟨j, c'⟩ := g
    change adUpDag a m (sigOf j c') = lsum _ _ (sigOf j c')
    rw [lsum_apply_of_bound _ 0 (fun i _ => adjFam_adUp_sigOf a m i j c')]
    simp
  | p n =>
    obtain ⟨j, c'⟩ := n
    change adUpDag a m (psiOf j c') = lsum _ _ (psiOf j c')
    rw [lsum_apply_of_bound _ (j + 1) (fun i hi => by
      rw [adjFam_adUp_psiOf, if_neg (by omega)])]
    simp only [adjFam_adUp_psiOf]
    rw [sum_range_ite_add_eq _ _ _ (by omega), adUpDag_psiOf]
    split
    · rename_i hmj
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      rw [lamP, show j + 1 - m = (j - m) + 1 by omega]
      push_cast
      ring
    · rfl

theorem isAdj_adUp (a : Fin 3) (m : ℕ) : IsAdj (adUp a m) (adUpDag a m) := by
  rw [← adjFam_adUp_eq]
  apply isAdj_of_rep (homDer_adUp a m)
  · intro k b
    rw [adUp_sigOf, lmul_zero]
    exact IsAdj.zero
  · intro k b
    rw [adUp_psiOf]
    have := isAdj_lmul_psis Finset.univ (fun c => epsilon a b c) (fun _ => k + m)
    simp only [conj_epsilon] at this
    exact this

theorem isAdj_adUpDag (a : Fin 3) (m : ℕ) : IsAdj (adUpDag a m) (adUp a m) :=
  (isAdj_adUp a m).symm

/-! ## `ad_a(m)† = adLowDag` -/

def YadLow (a : Fin 3) (m k : ℕ) (b : Fin 3) : Module.End ℂ W :=
  if m ≤ k then ∑ c, (epsilon a b c * lamP ⟨k - m, c⟩) • iP ⟨k - m, c⟩ else 0

theorem evZero_adjFam_adLow (a : Fin 3) (m : ℕ) :
    EvZero (adjFam (fun _ _ => 0) (fun k b => YadLow a m k b)) := by
  intro x
  obtain ⟨N, hx⟩ := exists_low x
  refine ⟨N + m, fun k hk => ?_⟩
  have h0 : ∀ c, iP ⟨k - m, c⟩ x = 0 := fun c => (kills_iP c) N (k - m) (by omega) x hx
  simp [adjFam, YadLow, h0, show m ≤ k by omega]

theorem isDer_adjFam_adLow (a : Fin 3) (m k : ℕ) :
    IsDer 0 (adjFam (fun _ _ => 0) (fun k b => YadLow a m k b) k) := by
  unfold adjFam YadLow
  simp only [mul_zero, zero_add]
  refine IsDer.sum _ _ fun b _ => IsDer.smul _ ?_
  split
  · simp only [Finset.mul_sum, mul_smul_comm]
    exact IsDer.sum _ _ fun c _ => (isDer_lmul_iP (isPar_psiOf k b) _).smul _
  · rw [mul_zero]; exact IsDer.zero 0

theorem adjFam_adLow_psiOf (a : Fin 3) (m k j : ℕ) (c' : Fin 3) :
    adjFam (fun _ _ => 0) (fun k b => YadLow a m k b) k (psiOf j c') =
      if m ≤ k ∧ k - m = j then
        ∑ b, (((k : ℂ) + 1) * (epsilon a b c' * lamP ⟨j, c'⟩)) • psiOf k b else 0 := by
  unfold adjFam YadLow
  by_cases hmk : m ≤ k
  · simp only [if_pos hmk, true_and, mul_zero, zero_add, LinearMap.sum_apply,
      Module.End.mul_apply, LinearMap.smul_apply, map_sum, map_smul, lmul_apply, iP_psiOf,
      ite_and, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    split_ifs with h
    · subst h
      simp [Finset.mul_sum, smul_smul, mul_comm]
    · simp
  · simp [hmk]

theorem adjFam_adLow_sigOf (a : Fin 3) (m k j : ℕ) (c' : Fin 3) :
    adjFam (fun _ _ => 0) (fun k b => YadLow a m k b) k (sigOf j c') = 0 := by
  by_cases hmk : m ≤ k <;> simp [adjFam, YadLow, hmk]

theorem adjFam_adLow_eq (a : Fin 3) (m : ℕ) :
    lsum _ (evZero_adjFam_adLow a m) = adLowDag a m := by
  symm
  apply (homDer_adLowDag a m).isDer.ext (IsDer.lsum _ (isDer_adjFam_adLow a m))
  intro g
  cases g with
  | s g =>
    obtain ⟨j, c'⟩ := g
    change adLowDag a m (sigOf j c') = lsum _ _ (sigOf j c')
    rw [lsum_apply_of_bound _ 0 (fun i _ => adjFam_adLow_sigOf a m i j c')]
    simp
  | p n =>
    obtain ⟨j, c'⟩ := n
    change adLowDag a m (psiOf j c') = lsum _ _ (psiOf j c')
    rw [lsum_apply_of_bound _ (j + m + 1) (fun i hi => by
      rw [adjFam_adLow_psiOf, if_neg (by omega)])]
    simp only [adjFam_adLow_psiOf]
    rw [sum_range_ite_sub_eq _ _ _ (by omega), adLowDag_psiOf]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [lamP]
    push_cast
    ring

theorem isAdj_adLow (a : Fin 3) (m : ℕ) : IsAdj (adLow a m) (adLowDag a m) := by
  rw [← adjFam_adLow_eq]
  apply isAdj_of_rep (homDer_adLow a m)
  · intro k b
    rw [adLow_sigOf, lmul_zero]
    exact IsAdj.zero
  · intro k b
    rw [adLow_psiOf]
    unfold YadLow
    split
    · have := isAdj_lmul_psis Finset.univ (fun c => epsilon a b c) (fun _ => k - m)
      simp only [conj_epsilon] at this
      exact this
    · rw [lmul_zero]; exact IsAdj.zero

/-! ## `d_a(-m)† = dUpDag` -/

def YdUp (a : Fin 3) (i k : ℕ) (b : Fin 3) : Module.End ℂ W :=
  ∑ c, (epsilon a b c * lamP ⟨k + i, c⟩) • iP ⟨k + i, c⟩

theorem evZero_adjFam_dUp (a : Fin 3) (i : ℕ) :
    EvZero (adjFam (fun k b => YdUp a i k b) (fun _ _ => 0)) := by
  intro x
  obtain ⟨N, hx⟩ := exists_low x
  refine ⟨N, fun k hk => ?_⟩
  simp only [adjFam, YdUp, mul_zero, smul_zero, add_zero, LinearMap.sum_apply,
    Module.End.mul_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
  rw [(kills_iP c) N (k + i) (by omega) x hx]
  simp

theorem isDer_adjFam_dUp (a : Fin 3) (i k : ℕ) :
    IsDer 1 (adjFam (fun k b => YdUp a i k b) (fun _ _ => 0) k) := by
  unfold adjFam YdUp
  simp only [mul_zero, smul_zero, add_zero, Finset.mul_sum, mul_smul_comm]
  exact IsDer.sum _ _ fun b _ => IsDer.sum _ _ fun c _ =>
    (isDer_lmul_iP ((isPar_sigOf k b).add_two) _).smul _

theorem adjFam_dUp_psiOf (a : Fin 3) (i k j : ℕ) (c' : Fin 3) :
    adjFam (fun k b => YdUp a i k b) (fun _ _ => 0) k (psiOf j c') =
      if k + i = j then ∑ b, (epsilon a b c' * lamP ⟨j, c'⟩) • sigOf k b else 0 := by
  simp only [adjFam, YdUp, mul_zero, smul_zero, add_zero, LinearMap.sum_apply,
    Module.End.mul_apply, LinearMap.smul_apply, map_sum, map_smul, lmul_apply, iP_psiOf,
    ite_and, smul_ite, smul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs with h
  · subst h
    simp [Finset.mul_sum, smul_smul]
  · simp

theorem adjFam_dUp_sigOf (a : Fin 3) (i k j : ℕ) (c' : Fin 3) :
    adjFam (fun k b => YdUp a i k b) (fun _ _ => 0) k (sigOf j c') = 0 := by
  simp [adjFam, YdUp]

theorem adjFam_dUp_eq (a : Fin 3) (i : ℕ) :
    lsum _ (evZero_adjFam_dUp a i) = dUpDag a (i + 1) := by
  symm
  apply (homDer_dUpDag a (i + 1)).isDer.ext (IsDer.lsum _ (isDer_adjFam_dUp a i))
  intro g
  cases g with
  | s g =>
    obtain ⟨j, c'⟩ := g
    change dUpDag a (i + 1) (sigOf j c') = lsum _ _ (sigOf j c')
    rw [lsum_apply_of_bound _ 0 (fun k _ => adjFam_dUp_sigOf a i k j c')]
    simp
  | p n =>
    obtain ⟨j, c'⟩ := n
    change dUpDag a (i + 1) (psiOf j c') = lsum _ _ (psiOf j c')
    rw [lsum_apply_of_bound _ (j + 1) (fun k hk => by
      rw [adjFam_dUp_psiOf, if_neg (by omega)])]
    simp only [adjFam_dUp_psiOf]
    rw [sum_range_ite_add_eq _ _ _ (by omega), dUpDag_psiOf]
    by_cases hij : i ≤ j
    · rw [if_pos hij, if_pos (by omega), show j + 1 - (i + 1) = j - i by omega]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [lamP]
    · rw [if_neg hij, if_neg (by omega)]

theorem isAdj_dUp (a : Fin 3) (i : ℕ) : IsAdj (dUp a (i + 1)) (dUpDag a (i + 1)) := by
  rw [← adjFam_dUp_eq]
  apply isAdj_of_rep (homDer_dUp a (i + 1))
  · intro k b
    rw [dUp_sigOf, show k + (i + 1) - 1 = k + i by omega]
    have := isAdj_lmul_psis Finset.univ (fun c => epsilon a b c) (fun _ => k + i)
    simp only [conj_epsilon] at this
    exact this
  · intro k b
    rw [dUp_psiOf, lmul_zero]
    exact IsAdj.zero

end KhanSL2.StrongMacdonald
