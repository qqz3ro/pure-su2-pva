module

public import KhanSL2.CanonicalTarget

@[expose] public section

/-! The canonical cocycles obey the three source generator bracket formulas. -/

noncomputable section

namespace KhanSL2.CanonicalBracket

open LambdaPolynomial

private theorem b_mem (a : Fin 3) :
    generator (.b 0 a) ∈ cochainPiece (1, 1, 1) := cochain_generator_mem _

private theorem c_mem (a : Fin 3) :
    generator (.c 0 a) ∈ cochainPiece (1, 0, 1) := cochain_generator_mem _

private theorem x_mem : xRepresentative ∈ cochainPiece (2, 1, 2) := by
  apply (cochainPiece _).neg_mem
  apply (cochainPiece _).sum_mem
  intro a _
  exact cochain_wedge_mem (b_mem a) (c_mem a)

private theorem mul_apply (u v : Cochain) : cochainData.mul u v = u * v := rfl

private theorem b_x (a : Fin 3) :
    BC.bracket (generator (.b 0 a)) xRepresentative =
      Finsupp.single 1 (generator (.b 0 a)) := by
  simp only [xRepresentative, map_neg, map_sum]
  simp_rw [BC.bracket_super_leibniz _ _ _ _ _ (b_mem a) (b_mem _)]
  simp only [BC.bracket_generator, BC.kernel_bb, mulRight_zero, zero_add]
  simp [BC.kernel_bc, koszulSign, mulLeft_single, mul_apply,
    show cochainOne = (1 : Cochain) from rfl, mul_smul_comm,
    Finsupp.single_sum, Finsupp.smul_single, apply_ite, eq_comm]

private theorem c_x (a : Fin 3) :
    BC.bracket (generator (.c 0 a)) xRepresentative =
      Finsupp.single 1 (generator (.c 0 a)) := by
  simp only [xRepresentative, map_neg, map_sum]
  simp_rw [BC.bracket_super_leibniz _ _ _ _ _ (c_mem a) (b_mem _)]
  simp only [BC.bracket_generator, BC.kernel_cc, mulLeft_zero, smul_zero, add_zero]
  fin_cases a <;> simp [Fin.sum_univ_three, BC.kernel_cb, koszulSign, mulRight_single, mul_apply,
    show cochainOne = (1 : Cochain) from rfl, smul_mul_assoc,
    Finsupp.single_sum, Finsupp.smul_single]

private theorem x_b (a : Fin 3) :
    BC.bracket xRepresentative (generator (.b 0 a)) =
      Finsupp.single 0 (translation (generator (.b 0 a))) +
        Finsupp.single 1 (generator (.b 0 a)) := by
  rw [BC.bracket_super_skew _ _ _ _ x_mem (b_mem a), b_x]
  simp [koszulSign, skew_single, Finset.sum_range_succ, add_comm]

private theorem x_c (a : Fin 3) :
    BC.bracket xRepresentative (generator (.c 0 a)) =
      Finsupp.single 0 (translation (generator (.c 0 a))) +
        Finsupp.single 1 (generator (.c 0 a)) := by
  rw [BC.bracket_super_skew _ _ _ _ x_mem (c_mem a), c_x]
  simp [koszulSign, skew_single, Finset.sum_range_succ, add_comm]

private theorem x_pair (a : Fin 3) :
    BC.bracket xRepresentative (wedge (generator (.b 0 a)) (generator (.c 0 a))) =
      Finsupp.single 0 (translation (wedge (generator (.b 0 a)) (generator (.c 0 a)))) +
        Finsupp.single 1 ((2 : ℂ) • wedge (generator (.b 0 a)) (generator (.c 0 a))) := by
  rw [BC.bracket_super_leibniz _ _ _ _ _ x_mem (b_mem a), x_b, x_c]
  norm_num only [koszulSign]
  simp only [translation_wedge]
  simp only [ite_true, one_smul,
    mulRight_add, mulLeft_add, mulRight_single, mulLeft_single, cochainData,
    translation_wedge, Finsupp.single_add, ← Finsupp.smul_single, wedge]
  module

/-- The even canonical cocycle has the centerless Virasoro bracket. -/
theorem x_x : BC.bracket xRepresentative xRepresentative =
    Finsupp.single 0 (translation xRepresentative) +
      Finsupp.single 1 ((2 : ℂ) • xRepresentative) := by
  change BC.bracket xRepresentative
    (-∑ a : Fin 3, wedge (generator (.b 0 a)) (generator (.c 0 a))) = _
  simp only [map_neg, map_sum, x_pair]
  simp only [xRepresentative, map_neg, map_sum, Finset.sum_add_distrib,
    Finsupp.single_neg, Finsupp.single_finsetSum, ← Finsupp.smul_single,
    smul_neg, Finset.smul_sum]
  module

/-- The odd canonical cocycle is primary of conformal weight three. -/
theorem x_y : BC.bracket xRepresentative yRepresentative =
    Finsupp.single 0 (translation yRepresentative) +
      Finsupp.single 1 ((3 : ℂ) • yRepresentative) := by
  rw [yRepresentative, BC.bracket_super_leibniz _ _ _ _ _ x_mem
    (cochain_wedge_mem (b_mem 0) (b_mem 1))]
  rw [BC.bracket_super_leibniz _ _ _ _ _ x_mem (b_mem 0)]
  simp only [x_b]
  norm_num only [koszulSign, Prod.fst_add]
  simp only [translation_wedge]
  simp only [ite_true, one_smul,
    mulRight_add, mulLeft_add, mulRight_single, mulLeft_single, cochainData,
    translation_wedge, Finsupp.single_add, ← Finsupp.smul_single, wedge,
    map_add, LinearMap.add_apply]
  module

private theorem y_mem : yRepresentative ∈ cochainPiece (3, 3, 3) :=
  cochain_wedge_mem (cochain_wedge_mem (b_mem 0) (b_mem 1)) (b_mem 2)

private theorem b_y (a : Fin 3) :
    BC.bracket (generator (.b 0 a)) yRepresentative = 0 := by
  rw [yRepresentative, BC.bracket_super_leibniz _ _ _ _ _ (b_mem a)
    (cochain_wedge_mem (b_mem 0) (b_mem 1))]
  rw [BC.bracket_super_leibniz _ _ _ _ _ (b_mem a) (b_mem 0)]
  simp

private theorem y_b (a : Fin 3) :
    BC.bracket yRepresentative (generator (.b 0 a)) = 0 := by
  rw [BC.bracket_super_skew _ _ _ _ y_mem (b_mem a), b_y]
  simp

/-- The odd canonical cocycle has zero bracket with itself. -/
theorem y_y : BC.bracket yRepresentative yRepresentative = 0 := by
  change BC.bracket yRepresentative
    (wedge (wedge (generator (.b 0 0)) (generator (.b 0 1))) (generator (.b 0 2))) = 0
  rw [BC.bracket_super_leibniz _ _ _ _ _ y_mem
    (cochain_wedge_mem (b_mem 0) (b_mem 1))]
  rw [BC.bracket_super_leibniz _ _ _ _ _ y_mem (b_mem 0)]
  simp [y_b]

/-- The descended even class obeys the source's prescribed bracket. -/
theorem target_x_x : targetBracket xClass xClass =
    Finsupp.single 0 (targetData.translation xClass) +
      Finsupp.single 1 ((2 : ℂ) • xClass) := by
  ext n
  simp only [xClass, target_bracket_classOf, x_x, Finsupp.add_apply]
  by_cases h0 : n = 0
  · subst n
    simp [target_translation_classOf]
  · by_cases h1 : n = 1
    · subst n
      simp only [Finsupp.single_apply, ite_eq_left rfl,
        ite_eq_right (by decide : (0 : ℕ) ≠ 1), zero_add]
      exact classOf_smul (2 : ℂ) xRepresentative xRepresentative_mem_cycles
    · simp [Finsupp.single_apply, h0, h1, Ne.symm h0, Ne.symm h1]

/-- The descended odd class is primary of conformal weight three. -/
theorem target_x_y : targetBracket xClass yClass =
    Finsupp.single 0 (targetData.translation yClass) +
      Finsupp.single 1 ((3 : ℂ) • yClass) := by
  ext n
  simp only [xClass, yClass, target_bracket_classOf, x_y, Finsupp.add_apply]
  by_cases h0 : n = 0
  · subst n
    simp [target_translation_classOf]
  · by_cases h1 : n = 1
    · subst n
      simp only [Finsupp.single_apply, ite_eq_left rfl,
        ite_eq_right (by decide : (0 : ℕ) ≠ 1), zero_add]
      exact classOf_smul (3 : ℂ) yRepresentative yRepresentative_mem_cycles
    · simp [Finsupp.single_apply, h0, h1, Ne.symm h0, Ne.symm h1]

/-- The descended odd class has zero bracket with itself. -/
theorem target_y_y : targetBracket yClass yClass = 0 := by
  ext n
  simp [yClass, target_bracket_classOf, y_y]

end KhanSL2.CanonicalBracket
