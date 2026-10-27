module

public import KhanSL2.Deformation.CohomologyOps

@[expose] public section

/-!
# `δ_ℓ` on the generator images (paper (5.2), blueprint `lem:deltasource`)

At cochain level, `δ₁ 𝒳 = -3 𝒴`, `δ₀ 𝒳 = -2 ∂𝒴` and `δ_ℓ 𝒴 = 0` for the representatives
`𝒳 = -Σ b₀ᵃ c₁ᵃ` and `𝒴 = b₀⁰ b₀¹ b₀²`. With `[δ₁, ∂] = δ₀` and `[δ₀, ∂] = 0` this gives, on
`x_j = ∂ʲ[𝒳]` and `y_j = ∂ʲ[𝒴]`,
`δ̄₁ x_j = -(2j+3) y_j`, `δ̄₀ x_j = -2 y_{j+1}`, `δ̄_ℓ y_j = 0`.
-/

noncomputable section

namespace KhanSL2

/-! ## Normal ordering of generator products -/

theorem generator_mul_self (m : Mode) : generator m * generator m = 0 := by
  have h := generator_mul_comm m m
  have h2 : (2 : ℂ) • (generator m * generator m) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

theorem generator_mul_generator_mul_self (m : Mode) (x : Cochain) :
    generator m * (generator m * x) = 0 := by
  rw [← mul_assoc, generator_mul_self, zero_mul]

theorem generator_mul_swap {m m' : Mode} (_h : m'.code < m.code) :
    generator m * generator m' = -(generator m' * generator m) := generator_mul_comm m m'

theorem generator_mul_mul_swap {m m' : Mode} (_h : m'.code < m.code) (x : Cochain) :
    generator m * (generator m' * x) = -(generator m' * (generator m * x)) := by
  rw [← mul_assoc, generator_mul_comm m m', neg_mul, mul_assoc]

/-! ## Cochain level -/

theorem xRepresentative_eq :
    xRepresentative = -∑ a : Fin 3, generator (.b 0 a) * generator (.c 0 a) := rfl

theorem yRepresentative_eq :
    yRepresentative = generator (.b 0 0) * (generator (.b 0 1) * generator (.b 0 2)) := by
  rw [yRepresentative, ← cochain_mul_eq_wedge, ← cochain_mul_eq_wedge, mul_assoc]

theorem delta_xRepresentative (ℓ : ℕ) :
    delta ℓ xRepresentative =
      (-(1 / 2) : ℂ) • ∑ a : Fin 3, generator (.b 0 a) * bbConv (1 - ℓ) a := by
  rw [xRepresentative_eq, map_neg, map_sum, Finset.smul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [delta_mul, delta_generator, delta_generator, deltaGenerator_b, deltaGenerator_c,
    cochainParity_generator]
  simp only [zero_mul, zero_add, neg_mul, mul_smul_comm, Nat.zero_add, neg_smul, mul_neg, neg_neg, smul_neg]

set_option maxHeartbeats 1000000 in
/-- `δ₁ 𝒳 = -3 𝒴`. -/
theorem delta_one_xRepresentative : delta 1 xRepresentative = (-3 : ℂ) • yRepresentative := by
  rw [delta_xRepresentative, yRepresentative_eq]
  simp only [Nat.sub_self, bbConv, Finset.range_one, Finset.sum_singleton, Nat.sub_zero, bbPair,
    Fin.sum_univ_three, Finset.mul_sum, mul_smul_comm, smul_add, mul_add]
  simp only [epsilon, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  simp only [generator_mul_generator_mul_self, generator_mul_self, mul_zero, smul_zero,
    zero_add, add_zero, generator_mul_mul_swap (by decide : (Mode.b 0 0).code < (Mode.b 0 1).code),
    generator_mul_mul_swap (by decide : (Mode.b 0 0).code < (Mode.b 0 2).code),
    generator_mul_mul_swap (by decide : (Mode.b 0 1).code < (Mode.b 0 2).code),
    generator_mul_swap (by decide : (Mode.b 0 0).code < (Mode.b 0 1).code),
    generator_mul_swap (by decide : (Mode.b 0 0).code < (Mode.b 0 2).code),
    generator_mul_swap (by decide : (Mode.b 0 1).code < (Mode.b 0 2).code),
    mul_neg, neg_neg, smul_neg]
  module


set_option maxHeartbeats 2000000 in
/-- `δ₀ 𝒳 = -2 ∂𝒴`. -/
theorem delta_zero_xRepresentative :
    delta 0 xRepresentative = (-2 : ℂ) • translation yRepresentative := by
  rw [delta_xRepresentative, yRepresentative_eq]
  simp only [translation_mul, translation_generator, translationGenerator,
    Mode.translationCoefficient, Mode.next, Nat.zero_add, Nat.cast_one, one_smul]
  simp only [Nat.sub_zero, bbConv, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
    Nat.sub_self, bbPair, Fin.sum_univ_three, Finset.mul_sum, mul_smul_comm, smul_add, mul_add,
    add_mul, Nat.reduceAdd, zero_add]
  simp only [epsilon, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  simp (disch := decide) only [generator_mul_generator_mul_self, generator_mul_self, mul_zero,
    smul_zero, zero_add, add_zero, generator_mul_mul_swap, generator_mul_swap, mul_neg, neg_neg,
    smul_neg, mul_assoc, neg_mul]
  module

theorem delta_yRepresentative (ℓ : ℕ) : delta ℓ yRepresentative = 0 := by
  rw [yRepresentative_eq]
  simp [delta_mul]

end KhanSL2
