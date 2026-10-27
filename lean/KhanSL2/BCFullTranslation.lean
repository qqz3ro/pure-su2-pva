module

public import KhanSL2.BCFullDifferential
public import KhanSL2.CETranslation

@[expose] public section

/-! The zero-ghost extension cancels the relative translation commutator. -/

noncomputable section

namespace KhanSL2

theorem fullGenerator_anticomm (m n : FullMode) :
    fullGenerator m * fullGenerator n = -(fullGenerator n * fullGenerator m) := by
  have h := FiniteExterior.wedge_generator_supercomm FullMode.code
    FullMode.code_injective m (fullGenerator n)
  change fullGenerator m * fullGenerator n =
    fullParity (fullGenerator n) * fullGenerator m at h
  simpa only [fullParity_generator, neg_mul] using h

theorem fullDifferential_translation_inclusion (u : Cochain) :
    fullDifferential (fullTranslation (fullInclusion u)) =
      fullTranslation (fullDifferential (fullInclusion u)) := by
  rw [← fullInclusion_translation, fullDifferential_inclusion, fullDifferential_inclusion]
  simp only [map_add, map_sum, fullTranslation_mul, fullTranslation_ghost,
    ← fullInclusion_translation, colorAction_translation]
  have h := congrArg fullInclusion (q_translation_commutator u)
  simp only [map_sub, map_sum, map_mul, fullInclusion_generator] at h
  have h' := sub_eq_iff_eq_add.mp h
  rw [h']
  simp only [Finset.sum_add_distrib]
  abel

theorem fullDifferential_translation_ghost (a : Fin 3) :
    fullDifferential (fullTranslation (ghost a)) =
      fullTranslation (fullDifferential (ghost a)) := by
  rw [fullTranslation_ghost, fullDifferential_generator]
  have hg : fullDifferential (ghost a) =
      -(1 / 2 : ℂ) • ∑ b : Fin 3, ∑ c : Fin 3,
        epsilon a b c • (ghost b * ghost c) := fullDifferential_generator (.inl a)
  rw [hg]
  simp only [fullDifferentialGenerator, qGenerator_c_zero, map_zero, zero_add,
    colorGenerator, Mode.color, Mode.recolor, map_sum, map_smul,
    fullTranslation_mul, fullTranslation_ghost, fullInclusion_generator,
    Finset.mul_sum, mul_smul_comm]
  have hcomm (b c : Fin 3) :
      fullGenerator (.inr (.c 0 b)) * ghost c =
        -(ghost c * fullGenerator (.inr (.c 0 b))) :=
    fullGenerator_anticomm (.inr (.c 0 b)) (.inl c)
  fin_cases a <;> norm_num [Fin.sum_univ_three, epsilon, hcomm] <;> module

theorem fullDifferential_translation_generator (m : FullMode) :
    fullDifferential (fullTranslation (fullGenerator m)) =
      fullTranslation (fullDifferential (fullGenerator m)) := by
  cases m with
  | inl a => exact fullDifferential_translation_ghost a
  | inr m =>
    simpa only [fullInclusion_generator] using
      fullDifferential_translation_inclusion (generator m)

/-- The Hamiltonian extension commutes with translation on all finite cochains. -/
theorem fullDifferential_fullTranslation (u : FullCochain) :
    fullDifferential (fullTranslation u) = fullTranslation (fullDifferential u) := by
  induction u using full_induction with
  | hzero => simp
  | hone => simp
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu =>
    change fullDifferential (fullTranslation (fullGenerator m * u)) =
      fullTranslation (fullDifferential (fullGenerator m * u))
    simp only [fullTranslation_mul, fullDifferential_mul, map_add,
      fullTranslation_parity, fullDifferential_translation_generator, hu]
    abel

end KhanSL2
