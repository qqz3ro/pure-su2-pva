module

public import KhanSL2.StrongMacdonald.LapGen

@[expose] public section

/-!
# Normal forms for quadratic elements of fixed weight

Quadratic elements `Σ C(t,e,f) • m(t,e,f)`, where `m(t,e,f)` is a product of two
generators whose loop indices add to `K` and `t` is the index of the odd factor
(or of the first odd factor). We record reindexing lemmas turning loop sums into this
normal form, and the `ε`-contractions that appear, written in the three tensors
`tA = δ_bf δ_ce`, `tB = δ_bc δ_ef`, `tC = δ_be δ_cf`.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

/-- The normal form with monomials `m`. -/
def NF (K : ℕ) (m : ℕ → Fin 3 → Fin 3 → W) (C : ℕ → Fin 3 → Fin 3 → ℂ) : W :=
  ∑ t ∈ Finset.range (K + 1), ∑ e, ∑ f, C t e f • m t e f

theorem NF_add (K : ℕ) (m : ℕ → Fin 3 → Fin 3 → W) (C D : ℕ → Fin 3 → Fin 3 → ℂ) :
    NF K m C + NF K m D = NF K m (fun t e f => C t e f + D t e f) := by
  simp only [NF, add_smul, Finset.sum_add_distrib]

theorem NF_sub (K : ℕ) (m : ℕ → Fin 3 → Fin 3 → W) (C D : ℕ → Fin 3 → Fin 3 → ℂ) :
    NF K m C - NF K m D = NF K m (fun t e f => C t e f - D t e f) := by
  simp only [NF, sub_smul, Finset.sum_sub_distrib]

theorem NF_smul (K : ℕ) (m : ℕ → Fin 3 → Fin 3 → W) (r : ℂ) (C : ℕ → Fin 3 → Fin 3 → ℂ) :
    r • NF K m C = NF K m (fun t e f => r * C t e f) := by
  simp only [NF, Finset.smul_sum, smul_smul]

theorem NF_neg (K : ℕ) (m : ℕ → Fin 3 → Fin 3 → W) (C : ℕ → Fin 3 → Fin 3 → ℂ) :
    -NF K m C = NF K m (fun t e f => -C t e f) := by
  simp only [NF, neg_smul, Finset.sum_neg_distrib]

theorem NF_congr (K : ℕ) (m : ℕ → Fin 3 → Fin 3 → W) {C D : ℕ → Fin 3 → Fin 3 → ℂ}
    (h : ∀ t, t ≤ K → ∀ e f, C t e f = D t e f) : NF K m C = NF K m D := by
  unfold NF
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)
  simp only [h t ht']

theorem NF_eq_zero (K : ℕ) (m : ℕ → Fin 3 → Fin 3 → W) {C : ℕ → Fin 3 → Fin 3 → ℂ}
    (h : ∀ t, t ≤ K → ∀ e f, C t e f = 0) : NF K m C = 0 := by
  rw [NF_congr K m (D := fun _ _ _ => 0) h]
  simp [NF]

theorem sum_range_ite_lt' {M : Type*} [AddCommMonoid M] (N n : ℕ) (hn : n ≤ N) (f : ℕ → M) :
    ∑ i ∈ Finset.range N, (if i < n then f i else 0) = ∑ i ∈ Finset.range n, f i := by
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Reindexing an increasing loop sum. -/
theorem NF_up (K : ℕ) (m : ℕ → Fin 3 → Fin 3 → W) (t0 A : ℕ) (hA : t0 + A ≤ K + 1)
    (D : ℕ → Fin 3 → Fin 3 → ℂ) :
    ∑ i ∈ Finset.range A, ∑ e, ∑ f, D i e f • m (t0 + i) e f =
      NF K m (fun t e f => if t0 ≤ t ∧ t < t0 + A then D (t - t0) e f else 0) := by
  obtain ⟨rest, hrest⟩ : ∃ rest, K + 1 = t0 + A + rest := ⟨K + 1 - (t0 + A), by omega⟩
  unfold NF
  rw [hrest, Finset.sum_range_add, Finset.sum_range_add]
  have h1 : ∑ t ∈ Finset.range t0, ∑ e, ∑ f,
      (if t0 ≤ t ∧ t < t0 + A then D (t - t0) e f else 0) • m t e f = 0 :=
    Finset.sum_eq_zero fun t ht => by
      have := Finset.mem_range.mp ht
      simp [show ¬ (t0 ≤ t ∧ t < t0 + A) by omega]
  have h3 : ∑ t ∈ Finset.range rest, ∑ e, ∑ f,
      (if t0 ≤ t0 + A + t ∧ t0 + A + t < t0 + A then D (t0 + A + t - t0) e f else 0) •
        m (t0 + A + t) e f = 0 :=
    Finset.sum_eq_zero fun t _ => by
      simp [show ¬ (t0 ≤ t0 + A + t ∧ t0 + A + t < t0 + A) by omega]
  rw [h1, h3, zero_add, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  simp [show t0 ≤ t0 + i ∧ t0 + i < t0 + A by omega]

/-- Reindexing a decreasing loop sum. -/
theorem NF_down (K : ℕ) (m : ℕ → Fin 3 → Fin 3 → W) (t0 A : ℕ) (hA : A ≤ t0 + 1) (hK : t0 ≤ K)
    (D : ℕ → Fin 3 → Fin 3 → ℂ) :
    ∑ i ∈ Finset.range A, ∑ e, ∑ f, D i e f • m (t0 - i) e f =
      NF K m (fun t e f => if t ≤ t0 ∧ t0 < t + A then D (t0 - t) e f else 0) := by
  rw [← Finset.sum_range_reflect]
  have h : ∀ i ∈ Finset.range A, (∑ e, ∑ f, D (A - 1 - i) e f • m (t0 - (A - 1 - i)) e f) =
      ∑ e, ∑ f, D (A - 1 - i) e f • m (t0 + 1 - A + i) e f := by
    intro i hi
    have := Finset.mem_range.mp hi
    rw [show t0 - (A - 1 - i) = t0 + 1 - A + i by omega]
  rw [Finset.sum_congr rfl h, NF_up K m (t0 + 1 - A) A (by omega)
    (fun i e f => D (A - 1 - i) e f)]
  apply NF_congr
  intro t _ e f
  by_cases h1 : t ≤ t0 ∧ t0 < t + A
  · rw [if_pos h1, if_pos (by omega), show A - 1 - (t - (t0 + 1 - A)) = t0 - t by omega]
  · rw [if_neg h1, if_neg (by omega)]

/-! ## Products of colour combinations -/

theorem sum_smul_mul_sum_smul (u v : Fin 3 → ℂ) (x y : Fin 3 → W) :
    (∑ e, u e • x e) * (∑ f, v f • y f) = ∑ e, ∑ f, (u e * v f) • (x e * y f) := by
  rw [Finset.sum_mul_sum]
  simp only [smul_mul_smul_comm]

theorem sum_smul_sum_sum {ι : Type*} (s : Finset ι) (r : ι → ℂ)
    (D : ι → Fin 3 → Fin 3 → ℂ) (x : Fin 3 → Fin 3 → W) :
    ∑ a ∈ s, r a • ∑ e, ∑ f, D a e f • x e f = ∑ e, ∑ f, (∑ a ∈ s, r a * D a e f) • x e f := by
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_comm]

/-! ## Contraction tensors -/

section Tensors
variable (b c : Fin 3)

def tA (e f : Fin 3) : ℂ := if b = f ∧ c = e then 1 else 0
def tB (e f : Fin 3) : ℂ := if b = c ∧ e = f then 1 else 0
def tC (e f : Fin 3) : ℂ := if b = e ∧ c = f then 1 else 0

end Tensors

end KhanSL2.StrongMacdonald
