module

public import KhanSL2.BCFullBracketLaws
public import KhanSL2.BCFullGeneration
public import Mathlib.Tactic.Module

@[expose] public section

/-! Both sesquilinearity identities for the concrete finite-mode bracket. -/

noncomputable section

namespace KhanSL2.FullBC

open LambdaPolynomial BC.PolynomialCalculus

theorem generatorActionMonomial_next_left (m : FullMode) (s : FullExteriorMonomial) :
    (m.translationCoefficient : ℂ) • generatorActionMonomial m.next s =
      -shift (generatorActionMonomial m s) := by
  change _ = -shiftLinear (generatorActionMonomial m s)
  simp only [generatorActionMonomial, Finset.smul_sum,
    map_sum, map_smul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [shiftLinear_apply, shift_single, Finsupp.smul_single,
    FullMode.order_next, smul_smul, ← Finsupp.single_neg, neg_smul]
  rw [show m.order + 1 + n.order = m.order + n.order + 1 by omega]
  congr 1
  rw [show (m.translationCoefficient : ℂ) *
      ((-1 : ℂ) ^ fullPosition n s * kernelCoefficient m.next n) =
      (-1 : ℂ) ^ fullPosition n s *
        ((m.translationCoefficient : ℂ) * kernelCoefficient m.next n) by ring]
  rw [kernelCoefficient_next_left]
  simp [neg_mul, mul_neg]

theorem generatorAction_next_left (m : FullMode) (u : FullCochain) :
    (m.translationCoefficient : ℂ) • generatorAction m.next u =
      -shift (generatorAction m u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv =>
    simp only [map_add, smul_add, shift_add, neg_add, hu, hv]
  | single s r =>
    simp only [generatorAction_single]
    rw [smul_comm, generatorActionMonomial_next_left, shift_smul, smul_neg]

theorem bracket_translation_generator_left (m : FullMode) (u : FullCochain) :
    bracket (fullTranslation (fullGenerator m)) u = -shift (bracket (fullGenerator m) u) := by
  rw [fullTranslation_generator]
  change bracket ((m.translationCoefficient : ℂ) • fullGenerator m.next) u = _
  simp only [map_smul, LinearMap.smul_apply, bracket_generator_left]
  exact generatorAction_next_left m u

theorem bracket_right_translation_generator {d : Degree} {a : FullCochain}
    (ha : a ∈ fullPiece d) (m : FullMode) :
    bracket a (fullTranslation (fullGenerator m)) =
      rightTranslation fullTranslation (bracket a (fullGenerator m)) := by
  have hm := full_generator_mem m
  have htm := fullTranslation_degree hm
  rw [bracket_super_skew d _ a _ ha htm,
    bracket_translation_generator_left]
  rw [bracket_super_skew d _ a _ ha hm]
  have hsign : koszulSign d ((1, (m.bCount : ℤ), (m.weight : ℤ)) + (0, 0, 1)) =
      koszulSign d (1, (m.bCount : ℤ), (m.weight : ℤ)) := by
    simp [koszulSign]
  rw [hsign, map_smul]
  congr 1
  simpa only [K_apply, fullData] using
    (rightTranslation_K fullData (bracket (fullGenerator m) a)).symm

theorem bracket_right_translation_of_mem {d : Degree} {a : FullCochain}
    (ha : a ∈ fullPiece d) (b : FullCochain) :
    bracket a (fullTranslation b) = rightTranslation fullTranslation (bracket a b) := by
  have hp : ∀e b, b ∈ fullPiece e →
      bracket a (fullTranslation b) = rightTranslation fullTranslation (bracket a b) := by
    intro e b hb
    apply full_homogeneous_induction
      (P := fun e b => b ∈ fullPiece e ∧
        bracket a (fullTranslation b) = rightTranslation fullTranslation (bracket a b))
      _ _ _ _ _ hb |>.2
    · intro e
      exact ⟨(fullPiece e).zero_mem, by simp⟩
    · exact ⟨full_one_mem, by simp⟩
    · intro e b c hb hc
      exact ⟨(fullPiece e).add_mem hb.1 hc.1, by
        simp only [map_add, hb.2, hc.2]⟩
    · intro e r b hb
      exact ⟨(fullPiece e).smul_mem r hb.1, by
        simp only [map_smul, hb.2]⟩
    · intro e m b hb
      refine ⟨full_wedge_mem (full_generator_mem m) hb.1, ?_⟩
      rw [fullTranslation_wedge, map_add]
      rw [bracket_super_leibniz d _ a _ b ha
        (fullTranslation_degree (full_generator_mem m)),
        bracket_super_leibniz d _ a _ _ ha (full_generator_mem m),
        bracket_super_leibniz d _ a _ _ ha (full_generator_mem m)]
      rw [bracket_right_translation_generator ha m, hb.2, map_add, map_smul]
      change _ = rightTranslation fullData.translation
        (mulRight fullData (bracket a (fullGenerator m)) b) +
        _ • rightTranslation fullData.translation
          (mulLeft fullData (fullGenerator m) (bracket a b))
      rw [rightTranslation_mulRight fullData fullTranslation_wedge,
        rightTranslation_mulLeft fullData fullTranslation_wedge]
      have hsign : koszulSign d
          ((1, (m.bCount : ℤ), (m.weight : ℤ)) + (0, 0, 1)) =
          koszulSign d (1, (m.bCount : ℤ), (m.weight : ℤ)) := by simp [koszulSign]
      rw [hsign]
      simp only [fullData, smul_add]
      abel
  have hb : b ∈ ⨆e, fullPiece e := by rw [full_piece_iSup_eq_top]; trivial
  refine Submodule.iSup_induction fullPiece
    (motive := fun b => bracket a (fullTranslation b) =
      rightTranslation fullTranslation (bracket a b)) hb
    (fun e b hb => hp e b hb) (by simp) ?_
  intro b c hb hc
  simp only [map_add, hb, hc]

theorem bracket_right_translation (a b : FullCochain) :
    bracket a (fullTranslation b) = rightTranslation fullTranslation (bracket a b) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | single s r => exact bracket_right_translation_of_mem (full_single_mem s r) b

theorem bracket_left_translation_of_mem {d e : Degree} {a b : FullCochain}
    (ha : a ∈ fullPiece d) (hb : b ∈ fullPiece e) :
    bracket (fullTranslation a) b = -shift (bracket a b) := by
  rw [bracket_super_skew _ e _ b (fullTranslation_degree ha) hb,
    bracket_right_translation]
  rw [bracket_super_skew d e a b ha hb]
  have hsign : koszulSign (d + (0, 0, 1)) e = koszulSign d e := by simp [koszulSign]
  rw [hsign]
  have hK : minusVariableMinusTranslation fullTranslation
      (rightTranslation fullTranslation (bracket b a)) =
        -shift (minusVariableMinusTranslation fullTranslation (bracket b a)) := by
    simpa only [K_apply, fullData] using K_rightTranslation fullData (bracket b a)
  rw [hK, shift_smul, smul_neg]

theorem bracket_left_translation (a b : FullCochain) :
    bracket (fullTranslation a) b = -shift (bracket a b) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a c ha hc =>
    simp only [map_add, LinearMap.add_apply, shift_add, neg_add, ha, hc]
  | single s r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b c hb hc => simp only [map_add, shift_add, neg_add, hb, hc]
    | single t u =>
      exact bracket_left_translation_of_mem (full_single_mem s r) (full_single_mem t u)

end KhanSL2.FullBC

