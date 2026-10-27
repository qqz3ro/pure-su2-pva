module

public import KhanSL2.CEConvolutionArithmetic

@[expose] public section

/-! The relative differential/translation commutator on every mode. -/

noncomputable section

namespace KhanSL2.CETranslation

def modeFamily : Bool → ℕ → Fin 3 → Mode
  | false => Mode.b
  | true => Mode.c

def offset : Bool → ℕ
  | false => 0
  | true => 1

def pairSum (kind : Bool) (i k : ℕ) (a : Fin 3) : Cochain :=
  ∑ b : Fin 3, ∑ c : Fin 3,
    epsilon a b c • (generator (.c i b) * generator (modeFamily kind k c))

def convolution (kind : Bool) (j : ℕ) (a : Fin 3) (i : ℕ) : Cochain :=
  pairSum kind i (j - i) a

theorem translation_family (kind : Bool) (j : ℕ) (a : Fin 3) :
    translation (generator (modeFamily kind j a)) =
      ((j + 1 + offset kind : ℕ) : ℂ) •
        generator (modeFamily kind (j + 1) a) := by
  cases kind <;> simp [modeFamily, offset, translationGenerator,
    Mode.translationCoefficient, Mode.next, Nat.add_assoc]

theorem translation_pairSum (kind : Bool) (i k : ℕ) (a : Fin 3) :
    translation (pairSum kind i k a) =
      ((i + 2 : ℕ) : ℂ) • pairSum kind (i + 1) k a +
        ((k + 1 + offset kind : ℕ) : ℂ) • pairSum kind i (k + 1) a := by
  simp only [pairSum, map_sum, map_smul, translation_mul,
    translation_family, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [translation_generator]
  simp only [translationGenerator, Mode.translationCoefficient, Mode.next,
    smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> ring

theorem translation_range (kind : Bool) (j : ℕ) (a : Fin 3) :
    translation (∑ i ∈ Finset.range j, pairSum kind i (j - 1 - i) a) =
      ((j + offset kind + 1 : ℕ) : ℂ) •
        (∑ i ∈ Finset.range (j + 1), convolution kind j a i) -
      convolution kind j a 0 - (offset kind : ℂ) • convolution kind j a j := by
  rw [map_sum]
  calc
    _ = ∑ i ∈ Finset.range j,
        (((i + 2 : ℕ) : ℂ) • convolution kind j a (i + 1) +
          ((j - i + offset kind : ℕ) : ℂ) • convolution kind j a i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have h₁ : j - 1 - i = j - (i + 1) := by omega
      have h₂ : j - (i + 1) + 1 = j - i := by omega
      rw [translation_pairSum]
      simp only [convolution, h₁, h₂]
    _ = _ := weighted_convolution_translation j (offset kind) (convolution kind j a)

theorem cc_convolution_endpoints (j : ℕ) (a : Fin 3) :
    convolution true j a j = convolution true j a 0 := by
  simp only [convolution, pairSum, Nat.sub_self, Nat.sub_zero, modeFamily]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  have h := cochain_supercomm (cochain_generator_mem (.c j c))
    (cochain_generator_mem (.c 0 b))
  have hm : generator (.c j c) * generator (.c 0 b) =
      -(generator (.c 0 b) * generator (.c j c)) := by
    simpa [koszulSign, cochain_mul_eq_wedge] using h
  rw [hm, epsilon_swap_right a c b]
  simp

theorem q_translation_b (j : ℕ) (a : Fin 3) :
    q (translation (generator (.b j a))) -
      translation (q (generator (.b j a))) = -convolution false j a 0 := by
  have ht := translation_range false j a
  simp only [offset, Nat.add_zero, Nat.cast_zero, zero_smul, sub_zero] at ht
  rw [translation_generator, translationGenerator, q_generator]
  simp only [Mode.translationCoefficient, Mode.next, map_smul, q_generator,
    qGenerator, map_neg]
  change ((j + 1 : ℕ) : ℂ) •
      (-(∑ i ∈ Finset.range (j + 1), pairSum false i (j + 1 - 1 - i) a)) -
      -(translation (∑ i ∈ Finset.range j, pairSum false i (j - 1 - i) a)) = _
  simp only [Nat.add_sub_cancel]
  change ((j + 1 : ℕ) : ℂ) •
      (-(∑ i ∈ Finset.range (j + 1), convolution false j a i)) -
      -(translation (∑ i ∈ Finset.range j, pairSum false i (j - 1 - i) a)) = _
  rw [ht]
  module

theorem q_translation_c (j : ℕ) (a : Fin 3) :
    q (translation (generator (.c j a))) -
      translation (q (generator (.c j a))) = -convolution true j a 0 := by
  have ht := translation_range true j a
  simp only [offset, Nat.cast_one, one_smul, cc_convolution_endpoints] at ht
  rw [translation_generator, translationGenerator, q_generator]
  simp only [Mode.translationCoefficient, Mode.next, map_smul, q_generator,
    qGenerator]
  change ((j + 2 : ℕ) : ℂ) •
      ((-(1 / 2 : ℂ)) •
        (∑ i ∈ Finset.range (j + 1), pairSum true i (j + 1 - 1 - i) a)) -
      ((-(1 / 2 : ℂ)) •
        translation (∑ i ∈ Finset.range j, pairSum true i (j - 1 - i) a)) = _
  simp only [Nat.add_sub_cancel]
  change ((j + 2 : ℕ) : ℂ) •
      ((-(1 / 2 : ℂ)) •
        (∑ i ∈ Finset.range (j + 1), convolution true j a i)) -
      ((-(1 / 2 : ℂ)) •
        translation (∑ i ∈ Finset.range j, pairSum true i (j - 1 - i) a)) = _
  rw [ht]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  module

theorem correction_family (kind : Bool) (j : ℕ) (a : Fin 3) :
    (∑ b : Fin 3, generator (.c 0 b) *
      colorAction b (generator (modeFamily kind j a))) =
        -convolution kind j a 0 := by
  simp only [colorAction_generator, colorGenerator, map_sum, convolution,
    Nat.sub_zero, pairSum, ← Finset.sum_neg_distrib]
  have hc : (modeFamily kind j a).color = a := by cases kind <;> rfl
  have hr : ∀ c, (modeFamily kind j a).recolor c = modeFamily kind j c := by
    intro c
    cases kind <;> rfl
  simp only [hc, hr, Finset.mul_sum, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [epsilon_swap_left b a c, neg_smul]

end KhanSL2.CETranslation

namespace KhanSL2

theorem q_translation_generator (m : Mode) :
    q (translation (generator m)) - translation (q (generator m)) =
      ∑ a : Fin 3, generator (.c 0 a) * colorAction a (generator m) := by
  cases m with
  | b j a =>
    rw [CETranslation.q_translation_b]
    exact (CETranslation.correction_family false j a).symm
  | c j a =>
    rw [CETranslation.q_translation_c]
    exact (CETranslation.correction_family true j a).symm

end KhanSL2
