module

public import KhanSL2.StrongMacdonald.Harmonic

@[expose] public section

/-!
# The FGT generators `S(n)` and `E(n)`

`S n` is the coefficient of `z^n` in `κ(X₀, X₀)` and `E n` the coefficient of `z^{n-1}` in
`κ(X₀, X₁)`, where `X₀ = Σ σ^a(-k) ξ_a z^k` and `X₁ = Σ (j+1) ψ^a(-(j+1)) ξ_a z^j`.
Both are harmonic invariants.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

/-- `S(n) = Σ_{k+l=n} Σ_a σ^a(-k) σ^a(-l)`. -/
def Sgen (n : ℕ) : W := ∑ k ∈ Finset.range (n + 1), ∑ a, sigOf k a * sigOf (n - k) a

/-- `E(n) = Σ_{k+j=n-1} Σ_a (j+1) σ^a(-k) ψ^a(-(j+1))`. -/
def Egen (n : ℕ) : W :=
  ∑ j ∈ Finset.range n, ∑ a, ((j : ℂ) + 1) • (sigOf (n - 1 - j) a * psiOf j a)

/-! ## Reindexing -/

theorem sum_range_ite_le_shift {M : Type*} [AddCommMonoid M] (n m : ℕ) (f : ℕ → M) :
    ∑ k ∈ Finset.range n, (if m ≤ k then f (k - m) else 0) =
      ∑ j ∈ Finset.range (n - m), f j := by
  rw [← Finset.sum_filter]
  have h : Finset.filter (fun k => m ≤ k) (Finset.range n) = Finset.Ico m n := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [h, Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl fun j _ => by rw [Nat.add_sub_cancel_left]

theorem sum_range_ite_le_sub {M : Type*} [AddCommMonoid M] (n m : ℕ) (g : ℕ → M) :
    ∑ k ∈ Finset.range (n + 1), (if m ≤ n - k then g k else 0) =
      ∑ k ∈ Finset.range (n + 1 - m), g k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega

/-- Swapping the two colour indices against `ε` changes the sign. -/
theorem sum_eps_swap (a : Fin 3) (F : Fin 3 → Fin 3 → W) :
    ∑ b, ∑ c, epsilon a b c • F c b = -∑ b, ∑ c, epsilon a b c • F b c := by
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [epsilon_swap_right, neg_smul]

/-! ## Values of the operators on generators -/

theorem X_sigOf' (i k : ℕ) (a b : Fin 3) :
    X i a (sigOf k b) = if i + 1 ≤ k then ∑ c, epsilon a b c • sigOf (k - (i + 1)) c else 0 := by
  simp [X]

theorem X_psiOf' (i k : ℕ) (a b : Fin 3) :
    X i a (psiOf k b) = if i + 1 ≤ k then
      -∑ c, (epsilon a c b * (((k + 1 - (i + 1) : ℕ) : ℂ) / ((k : ℂ) + 1))) •
        psiOf (k - (i + 1)) c else 0 := by
  simp only [X, LinearMap.sub_apply, Rlow_psiOf, adUpDag_psiOf, zero_sub]
  split_ifs <;> simp

theorem dUd_sigOf (i k : ℕ) (a b : Fin 3) : dUd i a (sigOf k b) = 0 := by
  simp [dUd]

theorem dUd_psiOf' (i k : ℕ) (a b : Fin 3) :
    dUd i a (psiOf k b) = if i + 1 ≤ k + 1 then
      ∑ c, (epsilon a c b * (1 / ((k : ℂ) + 1))) • sigOf (k + 1 - (i + 1)) c else 0 := by
  simp [dUd]

/-! ## `S(n)` is a harmonic invariant -/

theorem Y_Sgen (c : Fin 3) (n : ℕ) : Y c (Sgen n) = 0 := by
  simp only [Sgen, map_sum, (homDer_Y c).zero_mul_apply, Y_sigOf (k := _), Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  fin_cases c <;> simp [Fin.sum_univ_three, epsilon]

theorem X_Sgen (i : ℕ) (a : Fin 3) (n : ℕ) : X i a (Sgen n) = 0 := by
  have hX := (homDer_X i a).zero_mul_apply
  simp only [Sgen, map_sum, hX, X_sigOf', ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_add_distrib]
  -- move the conditions outside the colour sums
  have h1 : ∀ k, ∑ b, (if i + 1 ≤ k then (∑ c, epsilon a b c • sigOf (k - (i + 1)) c) *
      sigOf (n - k) b else 0) = if i + 1 ≤ k then ∑ b, ∑ c, epsilon a b c •
        (sigOf (k - (i + 1)) c * sigOf (n - k) b) else 0 := by
    intro k
    split_ifs
    · simp only [Finset.sum_mul, smul_mul_assoc]
    · simp
  have h2 : ∀ k, ∑ b, (if i + 1 ≤ n - k then sigOf k b *
      ∑ c, epsilon a b c • sigOf (n - k - (i + 1)) c else 0) = if i + 1 ≤ n - k then
        ∑ b, ∑ c, epsilon a b c • (sigOf k b * sigOf (n - k - (i + 1)) c) else 0 := by
    intro k
    split_ifs
    · simp only [Finset.mul_sum, mul_smul_comm]
    · simp
  simp only [h1, h2]
  have h3 : ∀ k ∈ Finset.range (n + 1), (if i + 1 ≤ k then ∑ b, ∑ c, epsilon a b c •
      (sigOf (k - (i + 1)) c * sigOf (n - k) b) else 0) = if i + 1 ≤ k then
        (fun j => ∑ b, ∑ c, epsilon a b c • (sigOf j c * sigOf (n - j - (i + 1)) b))
          (k - (i + 1)) else 0 := by
    intro k _
    split_ifs with hk
    · simp only [show n - k = n - (k - (i + 1)) - (i + 1) by omega]
    · rfl
  rw [Finset.sum_congr rfl h3, sum_range_ite_le_shift (n + 1) (i + 1)
      (fun j => ∑ b, ∑ c, epsilon a b c • (sigOf j c * sigOf (n - j - (i + 1)) b)),
    sum_range_ite_le_sub, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show n - j - (i + 1) = n - j - (i + 1) from rfl,
    sum_eps_swap a (fun b c => sigOf j b * sigOf (n - j - (i + 1)) c), neg_add_cancel]

theorem dUd_Sgen (i : ℕ) (a : Fin 3) (n : ℕ) : dUd i a (Sgen n) = 0 := by
  have hD : ∀ x y, dUd i a (x * y) = dUd i a x * y + parity x * dUd i a y :=
    fun x y => (homDer_dUd i a).isDer x y
  simp [Sgen, map_sum, hD, dUd_sigOf]

theorem Sgen_mem_inv (n : ℕ) : Sgen n ∈ inv := mem_inv.mpr fun c => Y_Sgen c n

theorem Sgen_mem_harm (n : ℕ) : Sgen n ∈ harm :=
  mem_harm_iff.mpr ⟨Sgen_mem_inv n, fun i a => X_Sgen i a n, fun i a => dUd_Sgen i a n⟩

/-! ## `E(n)` is a harmonic invariant -/

/-- A sum which is odd under reflection vanishes. -/
theorem sum_range_eq_zero_of_reflect (M : ℕ) (T : ℕ → W)
    (h : ∀ q < M, T (M - 1 - q) = -T q) : ∑ q ∈ Finset.range M, T q = 0 := by
  have h1 : ∑ q ∈ Finset.range M, T q = -∑ q ∈ Finset.range M, T q := by
    conv_lhs => rw [← Finset.sum_range_reflect]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun q hq => h q (Finset.mem_range.mp hq)
  have h2 : (2 : ℂ) • ∑ q ∈ Finset.range M, T q = 0 := by
    rw [two_smul]; nth_rewrite 1 [h1]; exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem sum_eps_swap' (a : Fin 3) (F : Fin 3 → Fin 3 → W) :
    ∑ b, ∑ c, epsilon a c b • F b c = -∑ b, ∑ c, epsilon a b c • F b c := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [epsilon_swap_right, neg_smul]

theorem psiOf_mul_sigOf' (j k : ℕ) (a b : Fin 3) :
    sigOf k b * psiOf j a = sigOf k b * psiOf j a := rfl

theorem Y_Egen (c : Fin 3) (n : ℕ) : Y c (Egen n) = 0 := by
  simp only [Egen, map_sum, map_smul, (homDer_Y c).zero_mul_apply, Y_sigOf (k := _), Y_psiOf,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  fin_cases c <;> simp [Fin.sum_univ_three, epsilon]

theorem dUd_Egen (i : ℕ) (a : Fin 3) (n : ℕ) : dUd i a (Egen n) = 0 := by
  have hD : ∀ x y, dUd i a (x * y) = dUd i a x * y + parity x * dUd i a y :=
    fun x y => (homDer_dUd i a).isDer x y
  have hpar : ∀ k b, parity (sigOf k b) = sigOf k b := fun k b => by
    simp [sigOf]
  have hterm : ∀ j ∈ Finset.range n, ∑ b, ((j : ℂ) + 1) •
      (dUd i a (sigOf (n - 1 - j) b) * psiOf j b +
        parity (sigOf (n - 1 - j) b) * dUd i a (psiOf j b)) =
      if i ≤ j then (fun q => -∑ b, ∑ c, epsilon a b c •
        (sigOf (n - 1 - (q + i)) b * sigOf q c)) (j - i) else 0 := by
    intro j _
    simp only [dUd_sigOf, zero_mul, zero_add, hpar, dUd_psiOf']
    by_cases hij : i ≤ j
    · rw [if_pos hij, ← sum_eps_swap' a]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [if_pos (by omega), Finset.mul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hj : ((j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
      rw [mul_smul_comm, smul_smul, show j + 1 - (i + 1) = j - i by omega,
        show n - 1 - (j - i + i) = n - 1 - j by omega]
      congr 1
      field_simp
    · rw [if_neg hij]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [if_neg (by omega), mul_zero, smul_zero]
  simp only [Egen, map_sum, map_smul, hD]
  rw [Finset.sum_congr rfl hterm, sum_range_ite_le_shift n i (fun q => -∑ b, ∑ c, epsilon a b c •
    (sigOf (n - 1 - (q + i)) b * sigOf q c)), Finset.sum_neg_distrib, neg_eq_zero]
  apply sum_range_eq_zero_of_reflect
  intro q hq
  rw [show n - 1 - (n - i - 1 - q + i) = q by omega, show n - i - 1 - q = n - 1 - (q + i) by omega]
  have hc : ∀ b c, sigOf q b * sigOf (n - 1 - (q + i)) c =
      sigOf (n - 1 - (q + i)) c * sigOf q b := fun b c => sig_commute _ _
  simp only [hc]
  exact sum_eps_swap a (fun b c => sigOf (n - 1 - (q + i)) b * sigOf q c)

theorem sum_range_ite_le_rev {M : Type*} [AddCommMonoid M] (n m : ℕ) (g : ℕ → M) :
    ∑ k ∈ Finset.range n, (if m ≤ n - 1 - k then g k else 0) =
      ∑ k ∈ Finset.range (n - m), g k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega

theorem X_Egen (i : ℕ) (a : Fin 3) (n : ℕ) : X i a (Egen n) = 0 := by
  have hX := (homDer_X i a).zero_mul_apply
  set G : ℕ → W := fun q => ∑ b, ∑ c, epsilon a b c •
    (((q : ℂ) + 1) • (sigOf (n - 1 - q - (i + 1)) c * psiOf q b)) with hG
  have hσ : ∀ j ∈ Finset.range n, ∑ b, ((j : ℂ) + 1) • (X i a (sigOf (n - 1 - j) b) * psiOf j b) =
      if i + 1 ≤ n - 1 - j then G j else 0 := by
    intro j _
    simp only [X_sigOf']
    split_ifs
    · simp only [hG, Finset.sum_mul, Finset.smul_sum, smul_mul_assoc]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      rw [smul_comm]
    · simp
  have hψ : ∀ j ∈ Finset.range n, ∑ b, ((j : ℂ) + 1) • (sigOf (n - 1 - j) b * X i a (psiOf j b)) =
      if i + 1 ≤ j then (fun q => -G q) (j - (i + 1)) else 0 := by
    intro j _
    simp only [X_psiOf']
    split_ifs with hij
    · have hj : ((j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero j
      have hcoef : ((j : ℂ) + 1) * (((j + 1 - (i + 1) : ℕ) : ℂ) / ((j : ℂ) + 1)) =
          ((j - (i + 1) : ℕ) : ℂ) + 1 := by
        rw [mul_div_cancel₀ _ hj, show j + 1 - (i + 1) = (j - (i + 1)) + 1 by omega]
        push_cast; ring
      simp only [hG, mul_neg, Finset.mul_sum, mul_smul_comm, smul_neg, Finset.smul_sum, smul_smul]
      conv_rhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [show n - 1 - (j - (i + 1)) - (i + 1) = n - 1 - j by omega, mul_left_comm, hcoef]
    · simp
  simp only [Egen, map_sum, map_smul, hX, smul_add, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl hσ, Finset.sum_congr rfl hψ, sum_range_ite_le_rev,
    sum_range_ite_le_shift n (i + 1) (fun q => -G q), ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun q _ => add_neg_cancel _

theorem Egen_mem_inv (n : ℕ) : Egen n ∈ inv := mem_inv.mpr fun c => Y_Egen c n

theorem Egen_mem_harm (n : ℕ) : Egen n ∈ harm :=
  mem_harm_iff.mpr ⟨Egen_mem_inv n, fun i a => X_Egen i a n, fun i a => dUd_Egen i a n⟩

end KhanSL2.StrongMacdonald
