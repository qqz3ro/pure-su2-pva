module

public import KhanSL2.CELeibniz

@[expose] public section

/-! Invariant cochains are closed under products, parity and translation. -/

noncomputable section

namespace KhanSL2

theorem colorAction_parity (a : Fin 3) (u : Cochain) :
    colorAction a (cochainParity u) = cochainParity (colorAction a u) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | single s r =>
    rw [cochainParity_of_mem (cochain_single_mem s r), map_smul,
      cochainParity_of_mem (colorAction_degree a (cochain_single_mem s r))]

theorem colorAction_translation_generator (a : Fin 3) (m : Mode) :
    colorAction a (translation (generator m)) =
      translation (colorAction a (generator m)) := by
  cases m <;>
    simp [translationGenerator, colorGenerator, Mode.next, Mode.recolor,
      Mode.color, Mode.translationCoefficient, Finset.smul_sum, smul_smul, mul_comm]

theorem colorAction_translation (a : Fin 3) (u : Cochain) :
    colorAction a (translation u) = translation (colorAction a u) := by
  induction u using cochain_induction with
  | hzero => simp
  | hone => simp [translation, colorAction]
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu =>
    change colorAction a (translation (generator m * u)) =
      translation (colorAction a (generator m * u))
    simp only [translation_mul, colorAction_mul, map_add,
      colorAction_translation_generator, hu]
    abel

theorem mem_relativeInvariants_iff (u : Cochain) :
    u ∈ relativeInvariants ↔ ∀ a, colorAction a u = 0 := by
  simp [relativeInvariants, Submodule.mem_iInf, LinearMap.mem_ker]

theorem invariant_wedge {u v : Cochain}
    (hu : u ∈ relativeInvariants) (hv : v ∈ relativeInvariants) :
    wedge u v ∈ relativeInvariants := by
  rw [mem_relativeInvariants_iff] at hu hv ⊢
  intro a
  rw [colorAction_wedge, hu a, hv a]
  simp [wedge]

theorem invariant_parity {u : Cochain} (hu : u ∈ relativeInvariants) :
    cochainParity u ∈ relativeInvariants := by
  rw [mem_relativeInvariants_iff] at hu ⊢
  intro a
  rw [colorAction_parity, hu a, map_zero]

theorem invariant_translation {u : Cochain} (hu : u ∈ relativeInvariants) :
    translation u ∈ relativeInvariants := by
  rw [mem_relativeInvariants_iff] at hu ⊢
  intro a
  rw [colorAction_translation, hu a, map_zero]

theorem cycle_wedge {u v : Cochain}
    (hu : u ∈ relativeCycles) (hv : v ∈ relativeCycles) :
    wedge u v ∈ relativeCycles := by
  refine ⟨invariant_wedge hu.1 hv.1, ?_⟩
  change q (wedge u v) = 0
  rw [q_wedge, LinearMap.mem_ker.mp hu.2, LinearMap.mem_ker.mp hv.2]
  simp [wedge]

theorem cycle_parity {u : Cochain} (hu : u ∈ relativeCycles) :
    cochainParity u ∈ relativeCycles := by
  refine ⟨invariant_parity hu.1, ?_⟩
  change q (cochainParity u) = 0
  rw [q_parity, LinearMap.mem_ker.mp hu.2, map_zero, neg_zero]

end KhanSL2
