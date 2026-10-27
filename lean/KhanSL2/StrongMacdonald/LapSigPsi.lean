module

public import KhanSL2.StrongMacdonald.NormalForm

@[expose] public section

/-!
# FGT Lemma 3.13 on a pair (even generator, odd generator)

For `x = σ^b(-k)` and `y = ψ^c(-(n+1))` the second-order defect of the difference
family, summed over the loop degree, is a quadratic element of weight `K = k + n`.
We bring every contribution into the normal form `Σ_t C(t) • σ(K-t) ψ(t)` and check
that the coefficients cancel, region by region in `t`.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

section SigPsi

variable (k n : ℕ) (b c : Fin 3)

/-- Monomials `σ^e(-(K-t)) ψ^f(-(t+1))`. -/
def mSP (K : ℕ) (t : ℕ) (e f : Fin 3) : W := sigOf (K - t) e * psiOf t f

theorem Td_psiOf (i j : ℕ) (a d : Fin 3) :
    Td i a (psiOf j d) = (1 / 2 : ℂ) • adLowDag a (i + 1) (psiOf j d) := by
  simp [Td]

theorem Xd_psiOf (i j : ℕ) (a d : Fin 3) : Xd i a (psiOf j d) = -adUp a (i + 1) (psiOf j d) := by
  simp [Xd]

theorem L_psiOf (i j : ℕ) (a d : Fin 3) : L i a (psiOf j d) = adLow a (i + 1) (psiOf j d) := by
  simp [L]

theorem X_psiOf (i j : ℕ) (a d : Fin 3) : X i a (psiOf j d) = -adUpDag a (i + 1) (psiOf j d) := by
  simp [X]

/-- The per-degree defect, split into its seven contributions. -/
theorem cross_Fam_sigOf_psiOf (i : ℕ) :
    cross (Fam i) (sigOf k b) (psiOf n c) =
      ∑ a, lam i • (E i a (sigOf k b) * iota i a (psiOf n c)) +
      ∑ a, lam i • (Rlow a (i + 1) (sigOf k b) * ((1 / 2 : ℂ) • adLowDag a (i + 1) (psiOf n c))) +
      ∑ a, lam i • (Rlow a (i + 1) (sigOf k b) * adUp a (i + 1) (psiOf n c)) +
      ∑ a, lam i • (Td i a (sigOf k b) * adLow a (i + 1) (psiOf n c)) +
      ∑ a, lam i • (Td i a (sigOf k b) * adUpDag a (i + 1) (psiOf n c)) -
      ∑ a, dU i a (sigOf k b) * dUd i a (psiOf n c) +
      ∑ a, ∑ b', ∑ c', (epsilon a b' c' * lam i) • (Y c' (sigOf k b) * KD i a b' (psiOf n c)) := by
  rw [cross_Fam_sigOf]
  simp only [L_sigOf, X_sigOf, Td_psiOf, Xd_psiOf, L_psiOf, X_psiOf,
    show ∀ a, Xd i a (sigOf k b) = Td i a (sigOf k b) from fun a => by
      rw [Td_sigOf, Xd_sigOf]]
  simp only [mul_neg, smul_neg, neg_smul, neg_neg, Finset.sum_neg_distrib, mul_add, smul_add,
    Finset.sum_add_distrib, sub_eq_add_neg, neg_add]
  abel

/-- Converting a summand into normal-form shape. -/
theorem sum_sig_psi_eq (A : Fin 3 → Fin 3 → ℂ) (s t : ℕ) (p : Fin 3 → ℂ) (u v : Fin 3 → Fin 3 → ℂ)
    (h : ∀ e f, ∑ a, p a * (u a e * v a f) = A e f) :
    ∑ a, p a • ((∑ e, u a e • sigOf s e) * (∑ f, v a f • psiOf t f)) =
      ∑ e, ∑ f, A e f • (sigOf s e * psiOf t f) := by
  simp only [sum_smul_mul_sum_smul]
  rw [sum_smul_sum_sum]
  simp only [h]

theorem psiOf_mul_sigOf (t s : ℕ) (e f : Fin 3) :
    psiOf t e * sigOf s f = sigOf s f * psiOf t e := (sig_commute _ _).symm

theorem sum_psi_sig_eq (A : Fin 3 → Fin 3 → ℂ) (s t : ℕ) (p : Fin 3 → ℂ) (u v : Fin 3 → Fin 3 → ℂ)
    (h : ∀ e f, ∑ a, p a * (u a f * v a e) = A e f) :
    ∑ a, p a • ((∑ e, u a e • psiOf t e) * (∑ f, v a f • sigOf s f)) =
      ∑ e, ∑ f, A e f • (sigOf s e * psiOf t f) := by
  simp only [sum_smul_mul_sum_smul]
  rw [sum_smul_sum_sum]
  simp only [psiOf_mul_sigOf]
  rw [Finset.sum_comm]
  simp only [h]

theorem sum_psi_sig_eq' (A : Fin 3 → Fin 3 → ℂ) (s t : ℕ) (u v : Fin 3 → Fin 3 → ℂ)
    (h : ∀ e f, ∑ a, u a f * v a e = A e f) :
    ∑ a, (∑ e, u a e • psiOf t e) * (∑ f, v a f • sigOf s f) =
      ∑ e, ∑ f, A e f • (sigOf s e * psiOf t f) := by
  have := sum_psi_sig_eq A s t (fun _ => 1) u v (fun e f => by simpa using h e f)
  simpa using this

theorem sum_smul_psi_sig_eq (A : Fin 3 → Fin 3 → ℂ) (s t : ℕ) (r : Fin 3 → ℂ)
    (w : Fin 3 → Fin 3 → Fin 3 → ℂ) (h : ∀ e f, ∑ x, r x * w x f e = A e f) :
    ∑ x, r x • ∑ a', ∑ c', w x a' c' • (psiOf t a' * sigOf s c') =
      ∑ e, ∑ f, A e f • (sigOf s e * psiOf t f) := by
  rw [sum_smul_sum_sum]
  simp only [psiOf_mul_sigOf]
  rw [Finset.sum_comm]
  simp only [h]

theorem sum_psi_mul_sig_eq (A : Fin 3 → Fin 3 → ℂ) (s t : ℕ) (q : Fin 3 → Fin 3 → ℂ)
    (v : Fin 3 → Fin 3 → ℂ) (h : ∀ e f, ∑ a', q a' e * v a' f = A e f) :
    ∑ a', ∑ e, q a' e • ((∑ f, v a' f • psiOf t f) * sigOf s e) =
      ∑ e, ∑ f, A e f • (sigOf s e * psiOf t f) := by
  simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul, psiOf_mul_sigOf]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.sum_smul, h]

theorem sum_rotate3 (F : Fin 3 → Fin 3 → Fin 3 → W) :
    ∑ x, ∑ y, ∑ z, F x y z = ∑ z, ∑ x, ∑ y, F x y z := by
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem sum_psi_mul_sum_sig_eq (A : Fin 3 → Fin 3 → ℂ) (s t : ℕ) (q : Fin 3 → Fin 3 → ℂ)
    (w : Fin 3 → Fin 3 → ℂ) (h : ∀ e f, ∑ x, q f x * w x e = A e f) :
    ∑ a', ∑ e, q a' e • (psiOf t a' * ∑ f, w e f • sigOf s f) =
      ∑ e, ∑ f, A e f • (sigOf s e * psiOf t f) := by
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul, psiOf_mul_sigOf]
  rw [sum_rotate3]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [← Finset.sum_smul, h]

theorem sum_sig_mul_psi_eq (A : Fin 3 → Fin 3 → ℂ) (s t : ℕ) (r : Fin 3 → Fin 3 → ℂ)
    (u : Fin 3 → Fin 3 → ℂ) (h : ∀ e f, ∑ x, r f x * u x e = A e f) :
    ∑ a, ∑ c', r a c' • ((∑ e, u c' e • sigOf s e) * psiOf t a) =
      ∑ e, ∑ f, A e f • (sigOf s e * psiOf t f) := by
  simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
  rw [sum_rotate3]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_smul, h]

def βB1 (n i : ℕ) : ℂ := lam i * (1 / 2) * (((n + 1 + (i + 1) : ℕ) : ℂ) / ((n : ℂ) + 1))

theorem sum_B1 (N : ℕ) (hk : k ≤ N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i •
        (Rlow a (i + 1) (sigOf k b) * ((1 / 2 : ℂ) • adLowDag a (i + 1) (psiOf n c))) =
      NF (k + n) (mSP (k + n)) (fun t e f => if n + 1 ≤ t ∧ t < n + 1 + k then
        βB1 n (t - (n + 1)) * (tA b c e f - tB b c e f) else 0) := by
  have step : ∀ i ∈ Finset.range N, ∑ a, lam i •
      (Rlow a (i + 1) (sigOf k b) * ((1 / 2 : ℂ) • adLowDag a (i + 1) (psiOf n c))) =
      if i < k then ∑ e, ∑ f, (βB1 n i * (tA b c e f - tB b c e f)) •
        mSP (k + n) (n + 1 + i) e f else 0 := by
    intro i _
    by_cases h : i < k
    · rw [if_pos h]
      simp only [Rlow_sigOf, if_pos (show i + 1 ≤ k by omega), adLowDag_psiOf, Finset.smul_sum,
        smul_smul]
      unfold mSP
      rw [show k + n - (n + 1 + i) = k - (i + 1) by omega, show n + 1 + i = n + (i + 1) by omega]
      apply sum_sig_psi_eq
      intro e f
      unfold βB1
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tA, tB] <;> ring
    · rw [if_neg h]
      simp [show ¬ (i + 1 ≤ k) by omega]
  rw [Finset.sum_congr rfl step, sum_range_ite_lt' N k hk,
    NF_up (k + n) (mSP (k + n)) (n + 1) k (by omega)]

theorem Td_sigOf' (i j : ℕ) (a d : Fin 3) :
    Td i a (sigOf j d) = ∑ e, (-epsilon a d e) • sigOf (j + (i + 1)) e := by
  rw [Td_sigOf, ← Finset.sum_neg_distrib]
  simp only [neg_smul]

theorem sum_B2 (N : ℕ) (hk : k ≤ N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i •
        (Rlow a (i + 1) (sigOf k b) * adUp a (i + 1) (psiOf n c)) =
      NF (k + n) (mSP (k + n)) (fun t e f => if n + 1 ≤ t ∧ t < n + 1 + k then
        lam (t - (n + 1)) * (tB b c e f - tA b c e f) else 0) := by
  have step : ∀ i ∈ Finset.range N, ∑ a, lam i •
      (Rlow a (i + 1) (sigOf k b) * adUp a (i + 1) (psiOf n c)) =
      if i < k then ∑ e, ∑ f, (lam i * (tB b c e f - tA b c e f)) •
        mSP (k + n) (n + 1 + i) e f else 0 := by
    intro i _
    by_cases h : i < k
    · rw [if_pos h]
      simp only [Rlow_sigOf, if_pos (show i + 1 ≤ k by omega), adUp_psiOf]
      unfold mSP
      rw [show k + n - (n + 1 + i) = k - (i + 1) by omega, show n + 1 + i = n + (i + 1) by omega]
      apply sum_sig_psi_eq
      intro e f
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tA, tB]
    · rw [if_neg h]
      simp [show ¬ (i + 1 ≤ k) by omega]
  rw [Finset.sum_congr rfl step, sum_range_ite_lt' N k hk,
    NF_up (k + n) (mSP (k + n)) (n + 1) k (by omega)]

theorem sum_C1 (N : ℕ) (hn : n ≤ N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i •
        (Td i a (sigOf k b) * adLow a (i + 1) (psiOf n c)) =
      NF (k + n) (mSP (k + n)) (fun t e f => if t ≤ n - 1 ∧ n - 1 < t + n then
        lam (n - 1 - t) * (tA b c e f - tB b c e f) else 0) := by
  have step : ∀ i ∈ Finset.range N, ∑ a, lam i •
      (Td i a (sigOf k b) * adLow a (i + 1) (psiOf n c)) =
      if i < n then ∑ e, ∑ f, (lam i * (tA b c e f - tB b c e f)) •
        mSP (k + n) (n - 1 - i) e f else 0 := by
    intro i _
    by_cases h : i < n
    · rw [if_pos h]
      simp only [Td_sigOf', adLow_psiOf, if_pos (show i + 1 ≤ n by omega)]
      unfold mSP
      rw [show k + n - (n - 1 - i) = k + (i + 1) by omega, show n - 1 - i = n - (i + 1) by omega]
      apply sum_sig_psi_eq
      intro e f
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tA, tB]
    · rw [if_neg h]
      simp [show ¬ (i + 1 ≤ n) by omega]
  rw [Finset.sum_congr rfl step, sum_range_ite_lt' N n hn,
    NF_down (k + n) (mSP (k + n)) (n - 1) n (by omega) (by omega)]

def βC2 (n i : ℕ) : ℂ := lam i * (((n + 1 - (i + 1) : ℕ) : ℂ) / ((n : ℂ) + 1))

theorem sum_C2 (N : ℕ) (hn : n ≤ N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i •
        (Td i a (sigOf k b) * adUpDag a (i + 1) (psiOf n c)) =
      NF (k + n) (mSP (k + n)) (fun t e f => if t ≤ n - 1 ∧ n - 1 < t + n then
        βC2 n (n - 1 - t) * (tB b c e f - tA b c e f) else 0) := by
  have step : ∀ i ∈ Finset.range N, ∑ a, lam i •
      (Td i a (sigOf k b) * adUpDag a (i + 1) (psiOf n c)) =
      if i < n then ∑ e, ∑ f, (βC2 n i * (tB b c e f - tA b c e f)) •
        mSP (k + n) (n - 1 - i) e f else 0 := by
    intro i _
    by_cases h : i < n
    · rw [if_pos h]
      simp only [Td_sigOf', adUpDag_psiOf, if_pos (show i + 1 ≤ n by omega)]
      unfold mSP
      rw [show k + n - (n - 1 - i) = k + (i + 1) by omega, show n - 1 - i = n - (i + 1) by omega]
      apply sum_sig_psi_eq
      intro e f
      unfold βC2
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tA, tB]
    · rw [if_neg h]
      simp [show ¬ (i + 1 ≤ n) by omega]
  rw [Finset.sum_congr rfl step, sum_range_ite_lt' N n hn,
    NF_down (k + n) (mSP (k + n)) (n - 1) n (by omega) (by omega)]

theorem sum_D (N : ℕ) (hn : n < N) :
    ∑ i ∈ Finset.range N, ∑ a, dU i a (sigOf k b) * dUd i a (psiOf n c) =
      NF (k + n) (mSP (k + n)) (fun t e f => if k ≤ t ∧ t < k + (n + 1) then
        (1 / ((n : ℂ) + 1)) * (tC b c e f - tB b c e f) else 0) := by
  have step : ∀ i ∈ Finset.range N, ∑ a, dU i a (sigOf k b) * dUd i a (psiOf n c) =
      if i < n + 1 then ∑ e, ∑ f, ((1 / ((n : ℂ) + 1)) * (tC b c e f - tB b c e f)) •
        mSP (k + n) (k + i) e f else 0 := by
    intro i _
    by_cases h : i < n + 1
    · rw [if_pos h]
      simp only [dU, dUd, dUp_sigOf, dUpDag_psiOf, if_pos (show i + 1 ≤ n + 1 by omega)]
      unfold mSP
      rw [show k + n - (k + i) = n + 1 - (i + 1) by omega, show k + i = k + (i + 1) - 1 by omega]
      apply sum_psi_sig_eq'
      intro e f
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tB, tC]
    · rw [if_neg h]
      simp [dUd, show ¬ (i + 1 ≤ n + 1) by omega]
  rw [Finset.sum_congr rfl step, sum_range_ite_lt' N (n + 1) (by omega),
    NF_up (k + n) (mSP (k + n)) k (n + 1) (by omega)]

theorem NF_single (K : ℕ) (m : ℕ → Fin 3 → Fin 3 → W) (t1 : ℕ) (ht : t1 ≤ K)
    (D : Fin 3 → Fin 3 → ℂ) :
    ∑ e, ∑ f, D e f • m t1 e f = NF K m (fun t e f => if t1 ≤ t ∧ t < t1 + 1 then D e f else 0) := by
  have := NF_up K m t1 1 (by omega) (fun _ => D)
  simpa using this

/-! ### The `E ι` contribution -/

theorem sum_A_iota (N : ℕ) (hn : n < N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i • (E i a (sigOf k b) * iota i a (psiOf n c)) =
      lam n • E n c (sigOf k b) := by
  simp only [iota_psiOf, mul_ite, mul_one, mul_zero, smul_ite, smul_zero, ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_range, hn, if_true, Finset.mem_univ]

theorem Td_mul (i : ℕ) (a : Fin 3) (x y : W) : Td i a (x * y) = Td i a x * y + x * Td i a y :=
  (homDer_Td i a).isDer x y

theorem dbar_Td_sigOf :
    dbar (Td n c (sigOf k b)) =
      NF (k + n) (mSP (k + n)) (fun _ e f => tC b c e f - tA b c e f) := by
  rw [Td_sigOf']
  simp only [map_sum, map_smul, dbar_sigOf]
  rw [Finset.sum_congr rfl (fun x _ => Finset.smul_sum), Finset.sum_comm]
  unfold NF
  rw [show k + (n + 1) = k + n + 1 by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  unfold mSP
  rw [show k + n + 1 - 1 - j = k + n - j by omega]
  apply sum_smul_psi_sig_eq
  intro e f
  fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
    simp [Fin.sum_univ_three, epsilon, tA, tC]

def βA2 (n j : ℕ) : ℂ := (1 / 2) * (((j + 1 + (n + 1) : ℕ) : ℂ) / ((j : ℂ) + 1))

theorem Td_dbar_sigOf :
    Td n c (dbar (sigOf k b)) =
      NF (k + n) (mSP (k + n)) (fun t e f => if n + 1 ≤ t ∧ t < n + 1 + k then
        βA2 n (t - (n + 1)) * (tB b c e f - tA b c e f) else 0) +
      NF (k + n) (mSP (k + n)) (fun t e f => if 0 ≤ t ∧ t < 0 + k then
        tC b c e f - tB b c e f else 0) := by
  rw [dbar_sigOf]
  simp only [map_sum, map_smul, Td_mul, smul_add, Finset.sum_add_distrib]
  congr 1
  · have step : ∀ j ∈ Finset.range k, ∑ a', ∑ e, epsilon a' b e •
        (Td n c (psiOf j a') * sigOf (k - 1 - j) e) =
        ∑ e, ∑ f, (βA2 n j * (tB b c e f - tA b c e f)) • mSP (k + n) (n + 1 + j) e f := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simp only [Td_psiOf, adLowDag_psiOf, Finset.smul_sum, smul_smul]
      unfold mSP
      rw [show k + n - (n + 1 + j) = k - 1 - j by omega, show n + 1 + j = j + (n + 1) by omega]
      apply sum_psi_mul_sig_eq
      intro e f
      unfold βA2
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tA, tB]
    rw [Finset.sum_congr rfl step, NF_up (k + n) (mSP (k + n)) (n + 1) k (by omega)]
  · have step : ∀ j ∈ Finset.range k, ∑ a', ∑ e, epsilon a' b e •
        (psiOf j a' * Td n c (sigOf (k - 1 - j) e)) =
        ∑ e, ∑ f, (tC b c e f - tB b c e f) • mSP (k + n) (0 + j) e f := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simp only [Td_sigOf']
      unfold mSP
      rw [show k + n - (0 + j) = k - 1 - j + (n + 1) by omega, zero_add]
      apply sum_psi_mul_sum_sig_eq
      intro e f
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tB, tC]
    rw [Finset.sum_congr rfl step, NF_up (k + n) (mSP (k + n)) 0 k (by omega)]

/-! ### The `K` contribution -/

theorem Y_sigOf (c' : Fin 3) : Y c' (sigOf k b) = ∑ e, epsilon c' b e • sigOf k e := by
  simp [Y]

theorem sum_K (N : ℕ) (hn : n < N) :
    ∑ i ∈ Finset.range N, ∑ a, ∑ b', ∑ c',
        (epsilon a b' c' * lam i) • (Y c' (sigOf k b) * KD i a b' (psiOf n c)) =
      NF (k + n) (mSP (k + n)) (fun t e f => if n ≤ t ∧ t < n + 1 then
        lam n * (tA b c e f - tB b c e f) else 0) := by
  simp only [KD, Module.End.mul_apply, lmul_apply, iota_psiOf, mul_ite, mul_one, mul_zero,
    smul_ite, smul_zero, ite_and]
  rw [Finset.sum_eq_single n (fun i _ hi => by simp [hi])
    (fun h => absurd (Finset.mem_range.mpr hn) h)]
  simp only [if_true]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Y_sigOf]
  rw [sum_sig_mul_psi_eq (fun e f => lam n * (tA b c e f - tB b c e f)) k n
      (fun a c' => epsilon a c c' * lam n) (fun c' e => epsilon c' b e) (fun e f => by
        fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
          simp [Fin.sum_univ_three, epsilon, tA, tB])]
  have := NF_single (k + n) (mSP (k + n)) n (by omega)
    (fun e f => lam n * (tA b c e f - tB b c e f))
  unfold mSP at this ⊢
  rw [show k + n - n = k by omega] at this
  simpa only [ite_and] using this

/-! ### Assembly -/

theorem lam_sub_succ (n t : ℕ) (h : n + 1 ≤ t) : lam (t - (n + 1)) = 1 / ((t : ℂ) - n) := by
  rw [lam, Nat.cast_sub h]; push_cast; ring_nf

theorem lam_pred_sub (n t : ℕ) (h : t < n) : lam (n - 1 - t) = 1 / ((n : ℂ) - t) := by
  rw [lam, show n - 1 - t = n - (t + 1) by omega, Nat.cast_sub (by omega)]; push_cast; ring_nf

theorem βB1_eq (n t : ℕ) (h : n + 1 ≤ t) :
    βB1 n (t - (n + 1)) = 1 / ((t : ℂ) - n) * (1 / 2) * (((t : ℂ) + 1) / ((n : ℂ) + 1)) := by
  rw [βB1, lam_sub_succ n t h, show n + 1 + (t - (n + 1) + 1) = t + 1 by omega]
  push_cast; ring

theorem βA2_eq (n t : ℕ) (h : n + 1 ≤ t) :
    βA2 n (t - (n + 1)) = (1 / 2) * (((t : ℂ) + 1) / ((t : ℂ) - n)) := by
  rw [βA2, show t - (n + 1) + 1 + (n + 1) = t + 1 by omega, Nat.cast_sub h]
  push_cast; ring_nf

theorem βC2_eq (n t : ℕ) (h : t < n) :
    βC2 n (n - 1 - t) = 1 / ((n : ℂ) - t) * (((t : ℂ) + 1) / ((n : ℂ) + 1)) := by
  rw [βC2, lam_pred_sub n t h, show n + 1 - (n - 1 - t + 1) = t + 1 by omega]
  push_cast; ring

/-- FGT Lemma 3.13 on a pair (even, odd). -/
theorem sum_cross_sigOf_psiOf (N : ℕ) (hk : k < N) (hn : n < N) :
    ∑ i ∈ Finset.range N, cross (Fam i) (sigOf k b) (psiOf n c) = 0 := by
  simp only [cross_Fam_sigOf_psiOf, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_A_iota k n b c N hn, sum_B1 k n b c N hk.le, sum_B2 k n b c N hk.le,
    sum_C1 k n b c N hn.le, sum_C2 k n b c N hn.le, sum_D k n b c N hn, sum_K k n b c N hn,
    E, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, dbar_Td_sigOf,
    Td_dbar_sigOf]
  simp only [NF_add, NF_sub, NF_smul]
  apply NF_eq_zero
  intro t ht e f
  generalize tA b c e f = A
  generalize tB b c e f = B
  generalize tC b c e f = C
  have hn1 := Nat.cast_add_one_ne_zero (R := ℂ) n
  rcases lt_trichotomy t n with htn | rfl | htn
  · have hR : t ≤ n - 1 ∧ n - 1 < t + n := by omega
    have hP : ¬ (n + 1 ≤ t ∧ t < n + 1 + k) := by omega
    have hU : ¬ (n ≤ t ∧ t < n + 1) := by omega
    have hd : (n : ℂ) - t ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast (Nat.ne_of_gt htn)
    rw [lam_pred_sub n t htn, βC2_eq n t htn]
    by_cases htk : t < k
    · simp only [if_pos hR, if_neg hP, if_neg hU, if_pos (show 0 ≤ t ∧ t < 0 + k by omega),
        if_neg (show ¬ (k ≤ t ∧ t < k + (n + 1)) by omega)]
      simp only [lam]
      field_simp
      ring
    · simp only [if_pos hR, if_neg hP, if_neg hU, if_neg (show ¬ (0 ≤ t ∧ t < 0 + k) by omega),
        if_pos (show k ≤ t ∧ t < k + (n + 1) by omega)]
      simp only [lam]
      field_simp
      ring
  · have hR : ¬ (t ≤ t - 1 ∧ t - 1 < t + t) := by omega
    have hP : ¬ (t + 1 ≤ t ∧ t < t + 1 + k) := by omega
    have hU : t ≤ t ∧ t < t + 1 := by omega
    by_cases htk : t < k
    · simp only [if_neg hR, if_neg hP, if_pos hU, if_pos (show 0 ≤ t ∧ t < 0 + k by omega),
        if_neg (show ¬ (k ≤ t ∧ t < k + (t + 1)) by omega)]
      simp only [lam]
      field_simp
      ring
    · simp only [if_neg hR, if_neg hP, if_pos hU, if_neg (show ¬ (0 ≤ t ∧ t < 0 + k) by omega),
        if_pos (show k ≤ t ∧ t < k + (t + 1) by omega)]
      simp only [lam]
      field_simp
      ring
  · have hR : ¬ (t ≤ n - 1 ∧ n - 1 < t + n) := by omega
    have hP : n + 1 ≤ t ∧ t < n + 1 + k := by omega
    have hU : ¬ (n ≤ t ∧ t < n + 1) := by omega
    have hd : (t : ℂ) - n ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast (Nat.ne_of_gt htn)
    rw [lam_sub_succ n t hP.1, βB1_eq n t hP.1, βA2_eq n t hP.1]
    by_cases htk : t < k
    · simp only [if_neg hR, if_pos hP, if_neg hU, if_pos (show 0 ≤ t ∧ t < 0 + k by omega),
        if_neg (show ¬ (k ≤ t ∧ t < k + (n + 1)) by omega)]
      simp only [lam]
      field_simp
      ring
    · simp only [if_neg hR, if_pos hP, if_neg hU, if_neg (show ¬ (0 ≤ t ∧ t < 0 + k) by omega),
        if_pos (show k ≤ t ∧ t < k + (n + 1) by omega)]
      simp only [lam]
      field_simp
      ring

end SigPsi

end KhanSL2.StrongMacdonald
