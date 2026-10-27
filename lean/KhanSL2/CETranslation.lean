module

public import KhanSL2.CETranslationGenerator
public import KhanSL2.CEEquivariance

@[expose] public section

/-!
# Translation on the relative CE complex

With the implemented epsilon convention, `[q,T] = Σ c₁ᵃ Lₐ`.
Consequently the commutator vanishes on the invariant subcomplex.
-/

noncomputable section

namespace KhanSL2

theorem translation_parity (u : Cochain) :
    translation (cochainParity u) = cochainParity (translation u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single s r =>
    rw [cochainParity_of_mem (cochain_single_mem s r), map_smul,
      cochainParity_of_mem (translation_degree (cochain_single_mem s r))]
    rfl

def translationCorrection : Module.End ℂ Cochain :=
  ∑ a : Fin 3, (wedgeLinear (generator (.c 0 a))).comp (colorAction a)

theorem translationCorrection_apply (u : Cochain) :
    translationCorrection u =
      ∑ a : Fin 3, generator (.c 0 a) * colorAction a u := by
  simp [translationCorrection, LinearMap.sum_apply, cochain_mul_eq_wedge, wedge]

theorem translationCorrection_one : translationCorrection cochainOne = 0 := by
  simp [translationCorrection_apply]

theorem translationCorrection_mul (u v : Cochain) :
    translationCorrection (u * v) =
      translationCorrection u * v + cochainParity u * translationCorrection v := by
  simp only [translationCorrection_apply, colorAction_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    exact (mul_assoc _ _ _).symm
  · apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    exact FiniteExterior.wedge_generator_supercomm Mode.code Mode.code_injective
      (.c 0 a) u

def qTranslationCommutator : Module.End ℂ Cochain :=
  q.comp translation - translation.comp q

theorem qTranslationCommutator_apply (u : Cochain) :
    qTranslationCommutator u = q (translation u) - translation (q u) := rfl

theorem qTranslationCommutator_one : qTranslationCommutator cochainOne = 0 := by
  simp [qTranslationCommutator_apply, translation]

theorem qTranslationCommutator_mul (u v : Cochain) :
    qTranslationCommutator (u * v) =
      qTranslationCommutator u * v + cochainParity u * qTranslationCommutator v := by
  simp only [qTranslationCommutator_apply, translation_mul, q_mul, map_add,
    translation_parity, sub_mul, mul_sub]
  abel

theorem q_translation_commutator (u : Cochain) :
    q (translation u) - translation (q u) =
      ∑ a : Fin 3, generator (.c 0 a) * colorAction a u := by
  change qTranslationCommutator u = _
  rw [← translationCorrection_apply]
  induction u using cochain_induction with
  | hzero => simp
  | hone => rw [qTranslationCommutator_one, translationCorrection_one]
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu =>
    change qTranslationCommutator (generator m * u) =
      translationCorrection (generator m * u)
    rw [qTranslationCommutator_mul, translationCorrection_mul, hu]
    rw [qTranslationCommutator_apply, q_translation_generator]
    simp only [translationCorrection_apply]

theorem q_translation_commutes {u : Cochain} (hu : u ∈ relativeInvariants) :
    q (translation u) = translation (q u) := by
  apply sub_eq_zero.mp
  rw [q_translation_commutator]
  rw [mem_relativeInvariants_iff] at hu
  simp only [hu, mul_zero, Finset.sum_const_zero]

theorem cycle_translation {u : Cochain} (hu : u ∈ relativeCycles) :
    translation u ∈ relativeCycles := by
  refine ⟨invariant_translation hu.1, ?_⟩
  change q (translation u) = 0
  rw [q_translation_commutes hu.1, LinearMap.mem_ker.mp hu.2, map_zero]

end KhanSL2
