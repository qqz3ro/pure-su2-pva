module

public import KhanSL2.BCBracketLaws
public import KhanSL2.CochainGeneration
public import Mathlib.Tactic.Module

@[expose] public section

/-! Both sesquilinearity identities for the concrete finite-mode bracket. -/

noncomputable section

namespace KhanSL2.BC

open LambdaPolynomial PolynomialCalculus

theorem generatorActionMonomial_next_left (m : Mode) (s : ExteriorMonomial) :
    (m.translationCoefficient : ℂ) • generatorActionMonomial m.next s =
      -shift (generatorActionMonomial m s) := by
  change _ = -shiftLinear (generatorActionMonomial m s)
  simp only [generatorActionMonomial, Finset.smul_sum,
    map_sum, map_smul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [shiftLinear_apply, shift_single, Finsupp.smul_single,
    Mode.order_next, smul_smul, ← Finsupp.single_neg, neg_smul]
  rw [show m.order + 1 + n.order = m.order + n.order + 1 by omega]
  congr 1
  rw [show (m.translationCoefficient : ℂ) *
      ((-1 : ℂ) ^ position n s * kernelCoefficient m.next n) =
      (-1 : ℂ) ^ position n s *
        ((m.translationCoefficient : ℂ) * kernelCoefficient m.next n) by ring]
  rw [kernelCoefficient_next_left]
  simp [neg_mul, mul_neg]

theorem generatorAction_next_left (m : Mode) (u : Cochain) :
    (m.translationCoefficient : ℂ) • generatorAction m.next u =
      -shift (generatorAction m u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, smul_add, shift_add, neg_add, hu, hv]
  | single s r =>
    simp only [generatorAction_single]
    rw [smul_comm, generatorActionMonomial_next_left, shift_smul, smul_neg]

theorem bracket_translation_generator_left (m : Mode) (u : Cochain) :
    bracket (translation (generator m)) u = -shift (bracket (generator m) u) := by
  rw [translation_generator]
  change bracket ((m.translationCoefficient : ℂ) • generator m.next) u = _
  simp only [map_smul, LinearMap.smul_apply, bracket_generator_left]
  exact generatorAction_next_left m u

theorem bracket_right_translation_generator {d : Degree} {a : Cochain}
    (ha : a ∈ cochainPiece d) (m : Mode) :
    bracket a (translation (generator m)) =
      rightTranslation translation (bracket a (generator m)) := by
  have hm := cochain_generator_mem m
  have htm := translation_degree hm
  rw [bracket_super_skew d _ a _ ha htm,
    bracket_translation_generator_left]
  rw [bracket_super_skew d _ a _ ha hm]
  have hsign : koszulSign d ((1, (m.bCount : ℤ), (m.weight : ℤ)) + (0, 0, 1)) =
      koszulSign d (1, (m.bCount : ℤ), (m.weight : ℤ)) := by
    simp [koszulSign]
  rw [hsign, map_smul]
  congr 1
  simpa only [K_apply, cochainData] using
    (rightTranslation_K cochainData (bracket (generator m) a)).symm

theorem bracket_right_translation_of_mem {d : Degree} {a : Cochain}
    (ha : a ∈ cochainPiece d) (b : Cochain) :
    bracket a (translation b) = rightTranslation translation (bracket a b) := by
  have hp : ∀e b, b ∈ cochainPiece e →
      bracket a (translation b) = rightTranslation translation (bracket a b) := by
    intro e b hb
    apply cochain_homogeneous_induction
      (P := fun e b => b ∈ cochainPiece e ∧
        bracket a (translation b) = rightTranslation translation (bracket a b))
      _ _ _ _ _ hb |>.2
    · intro e
      exact ⟨(cochainPiece e).zero_mem, by simp⟩
    · exact ⟨cochain_one_mem, by simp [translation]⟩
    · intro e b c hb hc
      exact ⟨(cochainPiece e).add_mem hb.1 hc.1, by
        simp only [map_add, hb.2, hc.2]⟩
    · intro e r b hb
      exact ⟨(cochainPiece e).smul_mem r hb.1, by
        simp only [map_smul, hb.2]⟩
    · intro e m b hb
      refine ⟨cochain_wedge_mem (cochain_generator_mem m) hb.1, ?_⟩
      rw [translation_wedge, map_add]
      rw [bracket_super_leibniz d _ a _ b ha
        (translation_degree (cochain_generator_mem m)),
        bracket_super_leibniz d _ a _ _ ha (cochain_generator_mem m),
        bracket_super_leibniz d _ a _ _ ha (cochain_generator_mem m)]
      rw [bracket_right_translation_generator ha m, hb.2, map_add, map_smul]
      change _ = rightTranslation cochainData.translation
        (mulRight cochainData (bracket a (generator m)) b) +
        _ • rightTranslation cochainData.translation
          (mulLeft cochainData (generator m) (bracket a b))
      rw [rightTranslation_mulRight cochainData translation_wedge,
        rightTranslation_mulLeft cochainData translation_wedge]
      have hsign : koszulSign d
          ((1, (m.bCount : ℤ), (m.weight : ℤ)) + (0, 0, 1)) =
          koszulSign d (1, (m.bCount : ℤ), (m.weight : ℤ)) := by simp [koszulSign]
      rw [hsign]
      simp only [cochainData, smul_add]
      abel
  have hb : b ∈ ⨆e, cochainPiece e := by rw [cochain_piece_iSup_eq_top]; trivial
  refine Submodule.iSup_induction cochainPiece
    (motive := fun b => bracket a (translation b) =
      rightTranslation translation (bracket a b)) hb
    (fun e b hb => hp e b hb) (by simp) ?_
  intro b c hb hc
  simp only [map_add, hb, hc]

theorem bracket_right_translation (a b : Cochain) :
    bracket a (translation b) = rightTranslation translation (bracket a b) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | single s r => exact bracket_right_translation_of_mem (cochain_single_mem s r) b

theorem bracket_left_translation_of_mem {d e : Degree} {a b : Cochain}
    (ha : a ∈ cochainPiece d) (hb : b ∈ cochainPiece e) :
    bracket (translation a) b = -shift (bracket a b) := by
  rw [bracket_super_skew _ e _ b (translation_degree ha) hb,
    bracket_right_translation]
  rw [bracket_super_skew d e a b ha hb]
  have hsign : koszulSign (d + (0, 0, 1)) e = koszulSign d e := by simp [koszulSign]
  rw [hsign]
  have hK : minusVariableMinusTranslation translation
      (rightTranslation translation (bracket b a)) =
        -shift (minusVariableMinusTranslation translation (bracket b a)) := by
    simpa only [K_apply, cochainData] using K_rightTranslation cochainData (bracket b a)
  rw [hK, shift_smul, smul_neg]

theorem bracket_left_translation (a b : Cochain) :
    bracket (translation a) b = -shift (bracket a b) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a c ha hc =>
    simp only [map_add, LinearMap.add_apply, shift_add, neg_add, ha, hc]
  | single s r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b c hb hc => simp only [map_add, shift_add, neg_add, hb, hc]
    | single t u =>
      exact bracket_left_translation_of_mem (cochain_single_mem s r) (cochain_single_mem t u)

end KhanSL2.BC
