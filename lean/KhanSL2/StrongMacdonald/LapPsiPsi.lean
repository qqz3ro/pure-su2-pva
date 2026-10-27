module

public import KhanSL2.StrongMacdonald.LapSigPsi

@[expose] public section

/-!
# FGT Lemma 3.13 on a pair of odd generators

For `x = ψ^b(-(r+1))` and `y = ψ^c(-(n+1))` the summed second-order defect is a quadratic
odd element of weight `K = r + n`. In the normal form `Σ_t C(t) • ψ(t) ψ(K-t)` an element
vanishes as soon as `C(t,e,f) = C(K-t,f,e)`, because the two monomials are negatives of
each other. We check this symmetry region by region.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

/-- Monomials `ψ^e(-(t+1)) ψ^f(-(K-t+1))`. -/
def mPP (K : ℕ) (t : ℕ) (e f : Fin 3) : W := psiOf t e * psiOf (K - t) f

theorem psiOf_anticomm (s t : ℕ) (e f : Fin 3) :
    psiOf s e * psiOf t f = -(psiOf t f * psiOf s e) := by
  have h := mul_psi (psiOf s e) ⟨t, f⟩
  rw [show parity (psiOf s e) = -psiOf s e from parity_psi _, mul_neg] at h
  exact h

/-- The antisymmetry criterion for the odd-odd normal form. -/
theorem NF_mPP_eq_zero (K : ℕ) (C : ℕ → Fin 3 → Fin 3 → ℂ)
    (h : ∀ t, t ≤ K → ∀ e f, C t e f = C (K - t) f e) : NF K (mPP K) C = 0 := by
  have hS : NF K (mPP K) C = -NF K (mPP K) C := by
    unfold NF
    conv_lhs => rw [← Finset.sum_range_reflect]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' : t ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
    unfold mPP
    rw [show K + 1 - 1 - t = K - t by omega, show K - (K - t) = t by omega, Finset.sum_comm,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [psiOf_anticomm, smul_neg, ← h t ht' e f]
  have h2 : (2 : ℂ) • NF K (mPP K) C = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hS]
    exact add_neg_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-! ## Generic conversion templates -/

theorem gen_prod (A : Fin 3 → Fin 3 → ℂ) (x y : Fin 3 → W) (p : Fin 3 → ℂ)
    (u v : Fin 3 → Fin 3 → ℂ) (h : ∀ e f, ∑ a, p a * (u a e * v a f) = A e f) :
    ∑ a, p a • ((∑ e, u a e • x e) * (∑ f, v a f • y f)) = ∑ e, ∑ f, A e f • (x e * y f) := by
  simp only [sum_smul_mul_sum_smul]
  rw [sum_smul_sum_sum]
  simp only [h]

theorem gen_left (A : Fin 3 → Fin 3 → ℂ) (x y : Fin 3 → W) (q v : Fin 3 → Fin 3 → ℂ)
    (h : ∀ e f, ∑ a, q a f * v a e = A e f) :
    ∑ a', ∑ c', q a' c' • ((∑ g, v a' g • x g) * y c') = ∑ e, ∑ f, A e f • (x e * y f) := by
  simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
  rw [sum_rotate3]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.sum_smul, h]

theorem gen_left2 (A : Fin 3 → Fin 3 → ℂ) (x y : Fin 3 → W) (r u : Fin 3 → Fin 3 → ℂ)
    (h : ∀ e f, ∑ c', r f c' * u c' e = A e f) :
    ∑ a, ∑ c', r a c' • ((∑ e, u c' e • x e) * y a) = ∑ e, ∑ f, A e f • (x e * y f) := by
  simp only [Finset.sum_mul, smul_mul_assoc, Finset.smul_sum, smul_smul]
  rw [sum_rotate3]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.sum_smul, h]

theorem gen_right (A : Fin 3 → Fin 3 → ℂ) (x y : Fin 3 → W) (q w : Fin 3 → Fin 3 → ℂ)
    (h : ∀ e f, ∑ c', q e c' * w c' f = A e f) :
    ∑ a', ∑ c', q a' c' • (x a' * ∑ g, w c' g • y g) = ∑ e, ∑ f, A e f • (x e * y f) := by
  simp only [Finset.mul_sum, mul_smul_comm, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.sum_smul, h]

theorem sum3_collect (w : Fin 3 → Fin 3 → Fin 3 → ℂ) (m : Fin 3 → Fin 3 → W) :
    ∑ g, ∑ e, ∑ f, w g e f • m e f = ∑ e, ∑ f, (∑ g, w g e f) • m e f := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_smul]

section PsiPsi

variable (r n : ℕ) (b c : Fin 3)

def ρE (r n : ℕ) : ℂ := ((n + 1 + (r + 1) : ℕ) : ℂ) / ((n : ℂ) + 1)
def τ1 (r j : ℕ) : ℂ := ((j + 1 + (r + 1) : ℕ) : ℂ) / ((j : ℂ) + 1)

theorem dbar_Td_psiOf :
    dbar (Td r b (psiOf n c)) =
      NF (r + n) (mPP (r + n)) (fun _ e f => (1 / 4) * ρE r n * (tC b c e f - tA b c e f)) := by
  rw [Td_psiOf]
  simp only [adLowDag_psiOf, map_smul, map_sum, dbar_psiOf, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  unfold NF
  rw [show n + (r + 1) = r + n + 1 by omega]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  unfold mPP
  rw [show r + n + 1 - 1 - j = r + n - j by omega, sum3_collect]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun f _ => ?_
  congr 1
  unfold ρE
  fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
    simp [Fin.sum_univ_three, epsilon, tA, tC] <;> ring

theorem Td_psiOf' (i j : ℕ) (a d : Fin 3) :
    Td i a (psiOf j d) = ∑ g, ((1 / 2 : ℂ) * (epsilon a g d * τ1 i j)) • psiOf (j + (i + 1)) g := by
  rw [Td_psiOf, adLowDag_psiOf, Finset.smul_sum]
  simp only [smul_smul, τ1]

theorem Td_dbar_psiOf :
    Td r b (dbar (psiOf n c)) =
      NF (r + n) (mPP (r + n)) (fun t e f => if r + 1 ≤ t ∧ t < r + 1 + n then
        (1 / 4) * τ1 r (t - (r + 1)) * (tB b c e f - tA b c e f) else 0) +
      NF (r + n) (mPP (r + n)) (fun t e f => if 0 ≤ t ∧ t < 0 + n then
        (1 / 4) * τ1 r (n - 1 - (t - 0)) * (tC b c e f - tB b c e f) else 0) := by
  rw [dbar_psiOf]
  simp only [map_smul, map_sum, Td_mul, smul_add, Finset.sum_add_distrib, Finset.smul_sum,
    smul_smul]
  congr 1
  · have step : ∀ j ∈ Finset.range n, ∑ a', ∑ c', ((1 / 2 : ℂ) * epsilon a' c c') •
        (Td r b (psiOf j a') * psiOf (n - 1 - j) c') =
        ∑ e, ∑ f, ((1 / 4) * τ1 r j * (tB b c e f - tA b c e f)) • mPP (r + n) (r + 1 + j) e f := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simp only [Td_psiOf']
      unfold mPP
      rw [show r + n - (r + 1 + j) = n - 1 - j by omega, show r + 1 + j = j + (r + 1) by omega]
      apply gen_left
      intro e f
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tA, tB] <;> ring
    rw [Finset.sum_congr rfl step, NF_up (r + n) (mPP (r + n)) (r + 1) n (by omega)]
  · have step : ∀ j ∈ Finset.range n, ∑ a', ∑ c', ((1 / 2 : ℂ) * epsilon a' c c') •
        (psiOf j a' * Td r b (psiOf (n - 1 - j) c')) =
        ∑ e, ∑ f, ((1 / 4) * τ1 r (n - 1 - j) * (tC b c e f - tB b c e f)) •
          mPP (r + n) (0 + j) e f := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      simp only [Td_psiOf']
      unfold mPP
      rw [show r + n - (0 + j) = n - 1 - j + (r + 1) by omega, zero_add]
      apply gen_right
      intro e f
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tB, tC] <;> ring
    rw [Finset.sum_congr rfl step, NF_up (r + n) (mPP (r + n)) 0 n (by omega)]

theorem E_psiOf :
    E r b (psiOf n c) =
      NF (r + n) (mPP (r + n)) (fun t e f => (1 / 4) * ρE r n * (tC b c e f - tA b c e f) -
        ((if r + 1 ≤ t ∧ t < r + 1 + n then
          (1 / 4) * τ1 r (t - (r + 1)) * (tB b c e f - tA b c e f) else 0) +
        (if 0 ≤ t ∧ t < 0 + n then
          (1 / 4) * τ1 r (n - 1 - (t - 0)) * (tC b c e f - tB b c e f) else 0))) := by
  rw [E, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, dbar_Td_psiOf,
    Td_dbar_psiOf, NF_add, NF_sub]

/-! ### Closed forms of the coefficients -/

theorem tA_swap (b c e f : Fin 3) : tA c b e f = tC b c e f := by
  simp only [tA, tC, and_comm]
theorem tB_swap (b c e f : Fin 3) : tB c b e f = tB b c e f := by
  simp only [tB, eq_comm]
theorem tC_swap (b c e f : Fin 3) : tC c b e f = tA b c e f := by
  simp only [tA, tC, and_comm]
theorem tB_flip (b c e f : Fin 3) : tB b c f e = tB b c e f := by
  simp only [tB]
  congr 1
  exact propext ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩

theorem ρE_eq : ρE r n = ((r : ℂ) + n + 2) / ((n : ℂ) + 1) := by
  rw [ρE]; push_cast; ring_nf

theorem τ1_eq (t : ℕ) (h : r + 1 ≤ t) : τ1 r (t - (r + 1)) = ((t : ℂ) + 1) / ((t : ℂ) - r) := by
  rw [τ1, show t - (r + 1) + 1 + (r + 1) = t + 1 by omega, Nat.cast_sub h]
  push_cast; ring_nf

theorem τ1_eq' (t : ℕ) (h : t < n) :
    τ1 r (n - 1 - (t - 0)) = ((r : ℂ) + n - t + 1) / ((n : ℂ) - t) := by
  rw [τ1, Nat.sub_zero, show n - 1 - t + 1 + (r + 1) = r + n + 1 - t by omega,
    show n - 1 - t = n - (t + 1) by omega, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring_nf

theorem βB1_eq' (t : ℕ) (h : t < r) :
    βB1 n (r - 1 - t) = 1 / ((r : ℂ) - t) * (1 / 2) * (((r : ℂ) + n - t + 1) / ((n : ℂ) + 1)) := by
  rw [βB1, lam_pred_sub r t h, show n + 1 + (r - 1 - t + 1) = r + n + 1 - t by omega,
    Nat.cast_sub (by omega)]
  push_cast; ring

theorem βC2_eq' (t : ℕ) (h : r + 1 ≤ t) (h2 : t ≤ r + n) :
    βC2 n (t - (r + 1)) = 1 / ((t : ℂ) - r) * (((r : ℂ) + n - t + 1) / ((n : ℂ) + 1)) := by
  rw [βC2, lam_sub_succ r t h, show n + 1 - (t - (r + 1) + 1) = r + n + 1 - t by omega,
    Nat.cast_sub (by omega)]
  push_cast; ring

/-- The `E` term at `(ψ_x, ψ_y)` in closed form. -/
theorem E_psiOf_closed :
    E r b (psiOf n c) =
      NF (r + n) (mPP (r + n)) (fun t e f =>
        (1 / 4) * (((r : ℂ) + n + 2) / ((n : ℂ) + 1)) * (tC b c e f - tA b c e f) -
        ((if r < t then (1 / 4) * (((t : ℂ) + 1) / ((t : ℂ) - r)) * (tB b c e f - tA b c e f)
          else 0) +
        (if t < n then (1 / 4) * (((r : ℂ) + n - t + 1) / ((n : ℂ) - t)) *
          (tC b c e f - tB b c e f) else 0))) := by
  rw [E_psiOf]
  apply NF_congr
  intro t ht e f
  rw [ρE_eq]
  congr 2
  · by_cases h : r < t
    · rw [if_pos (by omega), if_pos h, τ1_eq r t (by omega)]
    · rw [if_neg (by omega), if_neg h]
  · by_cases h : t < n
    · rw [if_pos (by omega), if_pos h, τ1_eq' r n t h]
    · rw [if_neg (by omega), if_neg h]

/-- The swapped `E` term in closed form, with the tensors of `(b, c)`. -/
theorem E_psiOf_closed_swap :
    E n c (psiOf r b) =
      NF (r + n) (mPP (r + n)) (fun t e f =>
        (1 / 4) * (((r : ℂ) + n + 2) / ((r : ℂ) + 1)) * (tA b c e f - tC b c e f) -
        ((if n < t then (1 / 4) * (((t : ℂ) + 1) / ((t : ℂ) - n)) * (tB b c e f - tC b c e f)
          else 0) +
        (if t < r then (1 / 4) * (((r : ℂ) + n - t + 1) / ((r : ℂ) - t)) *
          (tA b c e f - tB b c e f) else 0))) := by
  rw [E_psiOf_closed n r c b, Nat.add_comm n r]
  apply NF_congr
  intro t _ e f
  simp only [tA_swap b c, tB_swap b c, tC_swap b c]
  ring_nf

/-! ### The remaining contributions -/

theorem sum_P3 (N : ℕ) (hr : r ≤ N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i •
        (adLow a (i + 1) (psiOf r b) * ((1 / 2 : ℂ) • adLowDag a (i + 1) (psiOf n c))) =
      NF (r + n) (mPP (r + n)) (fun t e f => if t < r then
        1 / ((r : ℂ) - t) * (1 / 2) * (((r : ℂ) + n - t + 1) / ((n : ℂ) + 1)) *
          (tA b c e f - tB b c e f) else 0) := by
  have step : ∀ i ∈ Finset.range N, ∑ a, lam i •
      (adLow a (i + 1) (psiOf r b) * ((1 / 2 : ℂ) • adLowDag a (i + 1) (psiOf n c))) =
      if i < r then ∑ e, ∑ f, (βB1 n i * (tA b c e f - tB b c e f)) •
        mPP (r + n) (r - 1 - i) e f else 0 := by
    intro i _
    by_cases h : i < r
    · rw [if_pos h]
      simp only [adLow_psiOf, if_pos (show i + 1 ≤ r by omega), adLowDag_psiOf,
        Finset.smul_sum, smul_smul]
      unfold mPP
      rw [show r + n - (r - 1 - i) = n + (i + 1) by omega, show r - 1 - i = r - (i + 1) by omega]
      apply gen_prod
      intro e f
      unfold βB1
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tA, tB] <;> ring
    · rw [if_neg h]
      simp [show ¬ (i + 1 ≤ r) by omega]
  rw [Finset.sum_congr rfl step, sum_range_ite_lt' N r hr,
    NF_down (r + n) (mPP (r + n)) (r - 1) r (by omega) (by omega)]
  apply NF_congr
  intro t ht e f
  by_cases h : t < r
  · rw [if_pos (by omega), if_pos h, βB1_eq' r n t h]
  · rw [if_neg (by omega), if_neg h]

theorem sum_P4 (N : ℕ) (hn : n ≤ N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i •
        (((1 / 2 : ℂ) • adLowDag a (i + 1) (psiOf r b)) * adLow a (i + 1) (psiOf n c)) =
      NF (r + n) (mPP (r + n)) (fun t e f => if r < t then
        1 / ((t : ℂ) - r) * (1 / 2) * (((t : ℂ) + 1) / ((r : ℂ) + 1)) *
          (tA b c e f - tB b c e f) else 0) := by
  have step : ∀ i ∈ Finset.range N, ∑ a, lam i •
      (((1 / 2 : ℂ) • adLowDag a (i + 1) (psiOf r b)) * adLow a (i + 1) (psiOf n c)) =
      if i < n then ∑ e, ∑ f, (βB1 r i * (tA b c e f - tB b c e f)) •
        mPP (r + n) (r + 1 + i) e f else 0 := by
    intro i _
    by_cases h : i < n
    · rw [if_pos h]
      simp only [adLow_psiOf, if_pos (show i + 1 ≤ n by omega), adLowDag_psiOf,
        Finset.smul_sum, smul_smul]
      unfold mPP
      rw [show r + n - (r + 1 + i) = n - (i + 1) by omega, show r + 1 + i = r + (i + 1) by omega]
      apply gen_prod
      intro e f
      unfold βB1
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tA, tB] <;> ring
    · rw [if_neg h]
      simp [show ¬ (i + 1 ≤ n) by omega]
  rw [Finset.sum_congr rfl step, sum_range_ite_lt' N n hn,
    NF_up (r + n) (mPP (r + n)) (r + 1) n (by omega)]
  apply NF_congr
  intro t ht e f
  by_cases h : r < t
  · rw [if_pos (by omega), if_pos h, βB1_eq r t (by omega)]
  · rw [if_neg (by omega), if_neg h]

theorem sum_P5 (N : ℕ) (hr : r ≤ N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i •
        (adUpDag a (i + 1) (psiOf r b) * adUp a (i + 1) (psiOf n c)) =
      NF (r + n) (mPP (r + n)) (fun t e f => if t < r then
        1 / ((r : ℂ) - t) * (((t : ℂ) + 1) / ((r : ℂ) + 1)) *
          (tA b c e f - tB b c e f) else 0) := by
  have step : ∀ i ∈ Finset.range N, ∑ a, lam i •
      (adUpDag a (i + 1) (psiOf r b) * adUp a (i + 1) (psiOf n c)) =
      if i < r then ∑ e, ∑ f, (βC2 r i * (tA b c e f - tB b c e f)) •
        mPP (r + n) (r - 1 - i) e f else 0 := by
    intro i _
    by_cases h : i < r
    · rw [if_pos h]
      simp only [adUpDag_psiOf, if_pos (show i + 1 ≤ r by omega), adUp_psiOf]
      unfold mPP
      rw [show r + n - (r - 1 - i) = n + (i + 1) by omega, show r - 1 - i = r - (i + 1) by omega]
      apply gen_prod
      intro e f
      unfold βC2
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tA, tB]
    · rw [if_neg h]
      simp [show ¬ (i + 1 ≤ r) by omega]
  rw [Finset.sum_congr rfl step, sum_range_ite_lt' N r hr,
    NF_down (r + n) (mPP (r + n)) (r - 1) r (by omega) (by omega)]
  apply NF_congr
  intro t ht e f
  by_cases h : t < r
  · rw [if_pos (by omega), if_pos h, βC2_eq r t h]
  · rw [if_neg (by omega), if_neg h]

theorem sum_P6 (N : ℕ) (hn : n ≤ N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i •
        (adUp a (i + 1) (psiOf r b) * adUpDag a (i + 1) (psiOf n c)) =
      NF (r + n) (mPP (r + n)) (fun t e f => if r < t then
        1 / ((t : ℂ) - r) * (((r : ℂ) + n - t + 1) / ((n : ℂ) + 1)) *
          (tA b c e f - tB b c e f) else 0) := by
  have step : ∀ i ∈ Finset.range N, ∑ a, lam i •
      (adUp a (i + 1) (psiOf r b) * adUpDag a (i + 1) (psiOf n c)) =
      if i < n then ∑ e, ∑ f, (βC2 n i * (tA b c e f - tB b c e f)) •
        mPP (r + n) (r + 1 + i) e f else 0 := by
    intro i _
    by_cases h : i < n
    · rw [if_pos h]
      simp only [adUpDag_psiOf, if_pos (show i + 1 ≤ n by omega), adUp_psiOf]
      unfold mPP
      rw [show r + n - (r + 1 + i) = n - (i + 1) by omega, show r + 1 + i = r + (i + 1) by omega]
      apply gen_prod
      intro e f
      unfold βC2
      fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
        simp [Fin.sum_univ_three, epsilon, tA, tB]
    · rw [if_neg h]
      simp [show ¬ (i + 1 ≤ n) by omega]
  rw [Finset.sum_congr rfl step, sum_range_ite_lt' N n hn,
    NF_up (r + n) (mPP (r + n)) (r + 1) n (by omega)]
  apply NF_congr
  intro t ht e f
  by_cases h : r < t
  · rw [if_pos (by omega), if_pos h, βC2_eq' r n t (by omega) ht]
  · rw [if_neg (by omega), if_neg h]

theorem sum_P7 (N : ℕ) (hr : r < N) :
    ∑ i ∈ Finset.range N, ∑ a, ∑ b', ∑ c',
        (epsilon a b' c' * lam i) • (KD i a b' (psiOf r b) * Y c' (psiOf n c)) =
      NF (r + n) (mPP (r + n)) (fun t e f => if t = r then
        1 / ((r : ℂ) + 1) * (tA b c e f - tB b c e f) else 0) := by
  simp only [KD, Module.End.mul_apply, lmul_apply, iota_psiOf, mul_ite, mul_one, mul_zero,
    ite_mul, zero_mul, smul_ite, smul_zero, ite_and]
  rw [Finset.sum_eq_single r (fun i _ hi => by simp [hi])
    (fun h => absurd (Finset.mem_range.mpr hr) h)]
  simp only [if_true]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hY : ∀ c', Y c' (psiOf n c) = ∑ f, epsilon c' c f • psiOf n f := by
    intro c'; simp [Y]
  simp only [hY]
  rw [gen_right (fun e f => 1 / ((r : ℂ) + 1) * (tA b c e f - tB b c e f)) (psiOf r) (psiOf n)
      (fun a c' => epsilon a b c' * lam r) (fun c' f => epsilon c' c f) (fun e f => by
        unfold lam
        fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
          simp [Fin.sum_univ_three, epsilon, tA, tB])]
  have := NF_single (r + n) (mPP (r + n)) r (by omega)
    (fun e f => 1 / ((r : ℂ) + 1) * (tA b c e f - tB b c e f))
  unfold mPP at this ⊢
  rw [show r + n - r = n by omega] at this
  rw [this]
  apply NF_congr
  intro t _ e f
  by_cases h : t = r
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem sum_P8 (N : ℕ) (hn : n < N) :
    ∑ i ∈ Finset.range N, ∑ a, ∑ b', ∑ c',
        (epsilon a b' c' * lam i) • (Y c' (psiOf r b) * KD i a b' (psiOf n c)) =
      NF (r + n) (mPP (r + n)) (fun t e f => if t = r then
        1 / ((n : ℂ) + 1) * (tA b c e f - tB b c e f) else 0) := by
  simp only [KD, Module.End.mul_apply, lmul_apply, iota_psiOf, mul_ite, mul_one, mul_zero,
    smul_ite, smul_zero, ite_and]
  rw [Finset.sum_eq_single n (fun i _ hi => by simp [hi])
    (fun h => absurd (Finset.mem_range.mpr hn) h)]
  simp only [if_true]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hY : ∀ c', Y c' (psiOf r b) = ∑ e, epsilon c' b e • psiOf r e := by
    intro c'; simp [Y]
  simp only [hY]
  rw [gen_left2 (fun e f => 1 / ((n : ℂ) + 1) * (tA b c e f - tB b c e f)) (psiOf r) (psiOf n)
      (fun a c' => epsilon a c c' * lam n) (fun c' e => epsilon c' b e) (fun e f => by
        unfold lam
        fin_cases b <;> fin_cases c <;> fin_cases e <;> fin_cases f <;>
          simp [Fin.sum_univ_three, epsilon, tA, tB])]
  have := NF_single (r + n) (mPP (r + n)) r (by omega)
    (fun e f => 1 / ((n : ℂ) + 1) * (tA b c e f - tB b c e f))
  unfold mPP at this ⊢
  rw [show r + n - r = n by omega] at this
  rw [this]
  apply NF_congr
  intro t _ e f
  by_cases h : t = r
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem sum_P1 (N : ℕ) (hr : r < N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i • (iota i a (psiOf r b) * E i a (psiOf n c)) =
      lam r • E r b (psiOf n c) := by
  simp only [iota_psiOf, ite_mul, one_mul, zero_mul, smul_ite, smul_zero, ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_range, hr, if_true, Finset.mem_univ]

theorem sum_P2 (N : ℕ) (hn : n < N) :
    ∑ i ∈ Finset.range N, ∑ a, lam i • (E i a (psiOf r b) * iota i a (psiOf n c)) =
      lam n • E n c (psiOf r b) := by
  simp only [iota_psiOf, mul_ite, mul_one, mul_zero, smul_ite, smul_zero, ite_and]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_range, hn, if_true, Finset.mem_univ]

/-! ### Assembly -/

theorem cross_Fam_psiOf_psiOf (i : ℕ) :
    cross (Fam i) (psiOf r b) (psiOf n c) =
      ∑ a, lam i • (iota i a (psiOf r b) * E i a (psiOf n c)) -
      ∑ a, lam i • (E i a (psiOf r b) * iota i a (psiOf n c)) +
      ∑ a, lam i • (adLow a (i + 1) (psiOf r b) * ((1 / 2 : ℂ) • adLowDag a (i + 1) (psiOf n c))) +
      ∑ a, lam i • (((1 / 2 : ℂ) • adLowDag a (i + 1) (psiOf r b)) * adLow a (i + 1) (psiOf n c)) -
      ∑ a, lam i • (adUpDag a (i + 1) (psiOf r b) * adUp a (i + 1) (psiOf n c)) -
      ∑ a, lam i • (adUp a (i + 1) (psiOf r b) * adUpDag a (i + 1) (psiOf n c)) +
      ∑ a, ∑ b', ∑ c', (epsilon a b' c' * lam i) • (KD i a b' (psiOf r b) * Y c' (psiOf n c)) +
      ∑ a, ∑ b', ∑ c', (epsilon a b' c' * lam i) • (Y c' (psiOf r b) * KD i a b' (psiOf n c)) := by
  rw [cross_Fam_psiOf]
  simp only [L_psiOf, Td_psiOf, X_psiOf, Xd_psiOf, dU, dUp_psiOf, mul_zero,
    Finset.sum_const_zero, add_zero, neg_mul_neg]
  simp only [smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, neg_mul,
    mul_neg, neg_smul, smul_neg, Finset.sum_neg_distrib, neg_neg, sub_eq_add_neg, neg_add]
  abel

theorem NF_mPP_eq_zero' (K : ℕ) (C : ℕ → Fin 3 → Fin 3 → ℂ)
    (h : ∀ t u, t + u = K → ∀ e f, C t e f = C u f e) : NF K (mPP K) C = 0 :=
  NF_mPP_eq_zero K C fun t ht e f => h t (K - t) (by omega) e f

theorem tA_flip (b c e f : Fin 3) : tA b c f e = tC b c e f := rfl
theorem tC_flip (b c e f : Fin 3) : tC b c f e = tA b c e f := rfl

/-- FGT Lemma 3.13 on a pair of odd generators. -/
theorem sum_cross_psiOf_psiOf (N : ℕ) (hr : r < N) (hn : n < N) :
    ∑ i ∈ Finset.range N, cross (Fam i) (psiOf r b) (psiOf n c) = 0 := by
  simp only [cross_Fam_psiOf_psiOf, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_P1 r n b c N hr, sum_P2 r n b c N hn, sum_P3 r n b c N hr.le, sum_P4 r n b c N hn.le,
    sum_P5 r n b c N hr.le, sum_P6 r n b c N hn.le, sum_P7 r n b c N hr, sum_P8 r n b c N hn,
    E_psiOf_closed, E_psiOf_closed_swap]
  simp only [NF_add, NF_sub, NF_smul]
  apply NF_mPP_eq_zero'
  intro t u htu e f
  simp only [tA_flip b c e f, tB_flip b c e f, tC_flip b c e f]
  generalize tA b c e f = A
  generalize tB b c e f = B
  generalize tC b c e f = C
  have hcast : (u : ℂ) = r + n - t := by
    have := congrArg (Nat.cast (R := ℂ)) htu
    push_cast at this
    rw [eq_sub_iff_add_eq, add_comm]
    exact this
  have hr1 := Nat.cast_add_one_ne_zero (R := ℂ) r
  have hn1 := Nat.cast_add_one_ne_zero (R := ℂ) n
  simp only [lam]
  rcases lt_trichotomy t r with h1 | h1 | h1 <;> rcases lt_trichotomy t n with h2 | h2 | h2 <;>
  · simp (disch := omega) only [if_pos, if_neg]
    try have d1 : (r : ℂ) - t ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : r ≠ t))
    try have d2 : (t : ℂ) - r ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : t ≠ r))
    try have d3 : (n : ℂ) - t ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : n ≠ t))
    try have d4 : (t : ℂ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : t ≠ n))
    try have d5 : (r : ℂ) - u ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : r ≠ u))
    try have d6 : (u : ℂ) - r ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : u ≠ r))
    try have d7 : (n : ℂ) - u ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : n ≠ u))
    try have d8 : (u : ℂ) - n ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : u ≠ n))
    field_simp
    try rw [hcast]
    ring

end PsiPsi

end KhanSL2.StrongMacdonald
