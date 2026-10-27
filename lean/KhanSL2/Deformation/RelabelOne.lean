module

public import KhanSL2.Deformation.Delta
public import KhanSL2.ExteriorReindex

@[expose] public section

/-!
# `D₁` is the `B = 0` complex in disguise (blueprint `lem:D1relabel`, paper Lemma 5.1(ii))

The relabelling `ρ : b_j ↦ c'_{2j+1}`, `c_n ↦ c'_{2n}` (paper indices) is, in Lean's indexing,
`b j ↦ c (2j)`, `c j ↦ c (2j+1)`. It is order preserving on generator codes, so it is an
injective algebra map onto the pure-`c` subalgebra, and `ρ ∘ (Q + δ₁) = Q ∘ ρ`
(`relabelOne_totalOne`). Consequently `(Q + δ₁)² = 0`, so `Qδ₁ + δ₁Q = 0` on all cochains
(`q_delta_one_anticomm`).
-/

noncomputable section

namespace KhanSL2

theorem extendDerivation_eq_generic (f : Mode → Cochain) :
    extendDerivation f = FiniteExterior.extendDerivation Mode.code f := rfl

theorem extendDerivation_add (f g : Mode → Cochain) :
    extendDerivation (f + g) = extendDerivation f + extendDerivation g := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  simp only [extendDerivation, LinearMap.comp_apply, Finsupp.lsingle_apply,
    Finsupp.linearCombination_single, one_smul, LinearMap.add_apply, Pi.add_apply,
    wedge, map_add, LinearMap.add_apply, smul_add, Finset.sum_add_distrib]

/-- Exterior generators anticommute. -/
theorem generator_mul_comm (m m' : Mode) :
    generator m * generator m' = -(generator m' * generator m) := by
  have h := cochain_supercomm (cochain_generator_mem m) (cochain_generator_mem m')
  simpa [koszulSign, cochain_mul_eq_wedge] using h

/-- Swapping the two families in an `ε`-contracted pair of generators. -/
theorem epsilon_pair_swap (a : Fin 3) (g₁ g₂ : Fin 3 → Mode) :
    (∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c • (generator (g₁ b) * generator (g₂ c))) =
      ∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c • (generator (g₂ b) * generator (g₁ c)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  rw [generator_mul_comm, epsilon_swap_right, smul_neg, neg_smul, neg_neg]

/-- Splitting a sum over `range (2j)` into even and odd indices. -/
theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (j : ℕ) :
    (∑ i ∈ Finset.range (2 * j), f i) =
      (∑ i ∈ Finset.range j, f (2 * i)) + ∑ i ∈ Finset.range j, f (2 * i + 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ, Finset.sum_range_succ]
    abel

theorem sum_range_two_mul_add_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (j : ℕ) :
    (∑ i ∈ Finset.range (2 * j + 1), f i) =
      (∑ i ∈ Finset.range (j + 1), f (2 * i)) + ∑ i ∈ Finset.range j, f (2 * i + 1) := by
  rw [Finset.sum_range_succ, sum_range_two_mul, Finset.sum_range_succ (fun i => f (2 * i))]
  abel

/-! ## The relabelling -/

/-- `b j ↦ c (2j)`, `c j ↦ c (2j+1)`. -/
def relabelOneMode : Mode → Mode
  | .b j a => .c (2 * j) a
  | .c j a => .c (2 * j + 1) a

theorem relabelOneMode_code (m : Mode) :
    (relabelOneMode m).code + m.color.val = 2 * m.code + 3 := by
  cases m with
  | b j a => simp only [relabelOneMode, Mode.code, Mode.color]; omega
  | c j a => simp only [relabelOneMode, Mode.code, Mode.color]; omega

theorem relabelOneMode_code_lt (m m' : Mode) :
    (relabelOneMode m).code < (relabelOneMode m').code ↔ m.code < m'.code := by
  have h := relabelOneMode_code m
  have h' := relabelOneMode_code m'
  have hc := m.color.isLt
  have hc' := m'.color.isLt
  -- the colour is the code modulo three
  have hm : m.color.val = m.code % 3 := by
    cases m with
    | b j a => simp only [Mode.code, Mode.color]; omega
    | c j a => simp only [Mode.code, Mode.color]; omega
  have hm' : m'.color.val = m'.code % 3 := by
    cases m' with
    | b j a => simp only [Mode.code, Mode.color]; omega
    | c j a => simp only [Mode.code, Mode.color]; omega
  omega

theorem relabelOneMode_injective : Function.Injective relabelOneMode := by
  intro m m' h
  apply Mode.code_injective
  have h1 := (relabelOneMode_code_lt m m').not
  have h2 := (relabelOneMode_code_lt m' m).not
  rw [h] at h1 h2
  simp only [lt_irrefl, not_false_eq_true, true_iff, not_lt] at h1 h2
  omega

def relabelOneEmb : Mode ↪ Mode := ⟨relabelOneMode, relabelOneMode_injective⟩

/-- **The relabelling `ρ`** (blueprint `lem:D1relabel`). -/
def relabelOne : Cochain →ₗ[ℂ] Cochain := FiniteExterior.reindex relabelOneEmb

theorem relabelOne_generator (m : Mode) : relabelOne (generator m) = generator (relabelOneMode m) :=
  FiniteExterior.reindex_generator relabelOneEmb m

theorem relabelOne_mul (u v : Cochain) : relabelOne (u * v) = relabelOne u * relabelOne v :=
  FiniteExterior.reindex_wedge Mode.code Mode.code relabelOneEmb
    (fun a b => relabelOneMode_code_lt a b) u v

theorem relabelOne_injective : Function.Injective relabelOne :=
  FiniteExterior.reindex_injective relabelOneEmb

theorem relabelOne_single (s : ExteriorMonomial) (r : ℂ) :
    relabelOne (Finsupp.single s r) = Finsupp.single (s.map relabelOneEmb) r :=
  FiniteExterior.reindex_single relabelOneEmb s r

/-! ## `ρ ∘ (Q + δ₁) = Q ∘ ρ` -/

theorem relabelOne_qGenerator_b (j : ℕ) (a : Fin 3) :
    relabelOne (qGenerator (.b j a)) = qGenerator (.c (2 * j) a) := by
  simp only [qGenerator, map_neg, map_sum, map_smul]
  rw [sum_range_two_mul (fun i => ∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c •
    wedge (generator (.c i b)) (generator (.c (2 * j - 1 - i) c)))]
  have hrefl := Finset.sum_range_reflect (fun i => ∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c •
    wedge (generator (.c (2 * i) b)) (generator (.c (2 * j - 1 - 2 * i) c))) j
  rw [← hrefl]
  have hterm : ∀ i ∈ Finset.range j,
      (∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c •
        wedge (generator (.c (2 * (j - 1 - i)) b))
          (generator (.c (2 * j - 1 - 2 * (j - 1 - i)) c))) =
      ∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c •
        wedge (generator (.c (2 * i + 1) b)) (generator (.c (2 * j - 1 - (2 * i + 1)) c)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [show 2 * j - 1 - 2 * (j - 1 - i) = 2 * i + 1 by omega,
      show 2 * j - 1 - (2 * i + 1) = 2 * (j - 1 - i) by omega]
    exact epsilon_pair_swap a (fun b => .c (2 * (j - 1 - i)) b) (fun c => .c (2 * i + 1) c)
  rw [Finset.sum_congr rfl hterm, ← two_smul ℂ, smul_smul]
  norm_num
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [← cochain_mul_eq_wedge, ← cochain_mul_eq_wedge, relabelOne_mul, relabelOne_generator,
    relabelOne_generator]
  simp only [relabelOneMode, cochain_mul_eq_wedge]
  rw [show 2 * j - 1 - (2 * i + 1) = 2 * (j - 1 - i) by omega]

theorem relabelOne_qGenerator_c (j : ℕ) (a : Fin 3) :
    relabelOne (qGenerator (.c j a) + deltaGenerator 1 (.c j a)) =
      qGenerator (.c (2 * j + 1) a) := by
  simp only [qGenerator, deltaGenerator_c, bbConv, bbPair, map_add, map_sum, map_smul]
  rw [sum_range_two_mul_add_one (fun i => ∑ b : Fin 3, ∑ c : Fin 3, epsilon a b c •
    wedge (generator (.c i b)) (generator (.c (2 * j + 1 - 1 - i) c))), smul_add, add_comm]
  congr 2
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    rw [relabelOne_mul, relabelOne_generator, relabelOne_generator]
    simp only [relabelOneMode, cochain_mul_eq_wedge]
    rw [show j + 1 - 1 = j by omega, show 2 * j + 1 - 1 - 2 * i = 2 * (j - i) by omega]
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    rw [← cochain_mul_eq_wedge, relabelOne_mul, relabelOne_generator, relabelOne_generator]
    simp only [relabelOneMode, cochain_mul_eq_wedge]
    rw [show 2 * j + 1 - 1 - (2 * i + 1) = 2 * (j - 1 - i) + 1 by omega]

theorem relabelOne_generator_identity (m : Mode) :
    relabelOne (qGenerator m + deltaGenerator 1 m) = qGenerator (relabelOneMode m) := by
  cases m with
  | b j a =>
    rw [deltaGenerator_b, add_zero]
    exact relabelOne_qGenerator_b j a
  | c j a => exact relabelOne_qGenerator_c j a

/-- The total differential `D₁ = Q + δ₁`. -/
def totalOne : Cochain →ₗ[ℂ] Cochain := q + delta 1

theorem totalOne_apply (u : Cochain) : totalOne u = q u + delta 1 u := rfl

/-- **`ρ ∘ D₁ = Q ∘ ρ`.** -/
theorem relabelOne_totalOne (u : Cochain) : relabelOne (totalOne u) = q (relabelOne u) := by
  have h : totalOne = extendDerivation (qGenerator + deltaGenerator 1) := by
    rw [extendDerivation_add]
    rfl
  rw [h]
  exact FiniteExterior.reindex_extendDerivation Mode.code Mode.code relabelOneEmb
    (fun a b => relabelOneMode_code_lt a b) _ qGenerator
    (fun m => relabelOne_generator_identity m) u

/-- **`Qδ₁ + δ₁Q = 0`** on all cochains. -/
theorem q_delta_one_anticomm (u : Cochain) : q (delta 1 u) + delta 1 (q u) = 0 := by
  have hsq : totalOne (totalOne u) = 0 := by
    apply relabelOne_injective
    rw [relabelOne_totalOne, relabelOne_totalOne, q_square_zero, map_zero]
  simp only [totalOne_apply, map_add, q_square_zero, delta_delta (le_refl 1)] at hsq
  rw [← hsq]
  abel

end KhanSL2
