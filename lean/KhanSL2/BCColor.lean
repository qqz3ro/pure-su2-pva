module

public import KhanSL2.CochainBracketDerivation
public import KhanSL2.CEInvariantBasics

@[expose] public section

/-! The actual color action preserves the normalized `bc` bracket. -/

noncomputable section

namespace KhanSL2

theorem colorAction_bracket_generators (a : Fin 3) (m n : Mode) :
    bracketDerivationDefect (colorAction a) BC.bracket
      (generator m) (generator n) = 0 := by
  rw [bracketDerivationDefect_eq_zero]
  rw [BC.bracket_generator, colorAction_generator, colorAction_generator]
  have h0 : colorAction a cochainOne = 0 := by simp [colorAction]
  simp only [BC.kernel, coefficientMap_single, map_smul, h0, smul_zero,
    Finsupp.single_zero]
  cases m with
  | b j b =>
    cases n with
    | b k c =>
      simp [colorGenerator, Mode.recolor, Mode.color, map_sum, LinearMap.sum_apply]
    | c k c =>
      fin_cases a <;> fin_cases b <;> fin_cases c <;>
        simp [colorGenerator, Mode.recolor, Mode.color, Fin.sum_univ_succ,
          epsilon, BC.kernel, BC.kernelCoefficient, Mode.pairsWith, Mode.order,
          smul_smul, ← add_smul]
  | c j b =>
    cases n with
    | b k c =>
      fin_cases a <;> fin_cases b <;> fin_cases c <;>
        simp [colorGenerator, Mode.recolor, Mode.color, Fin.sum_univ_succ,
          epsilon, BC.kernel, BC.kernelCoefficient, Mode.pairsWith, Mode.order,
          smul_smul, ← add_smul]
    | c k c =>
      simp [colorGenerator, Mode.recolor, Mode.color, map_sum, LinearMap.sum_apply]

theorem colorAction_bracket (a : Fin 3) (u v : Cochain) (n : ℕ) :
    colorAction a (BC.bracket u v n) =
      BC.bracket (colorAction a u) v n + BC.bracket u (colorAction a v) n := by
  have h := CochainBracketDerivation.of_generators (colorAction a) cochain_isPVA
    (colorAction_wedge a) (fun _ _ hu => colorAction_degree a hu)
    (colorAction_translation a) (by simp [colorAction])
    (colorAction_bracket_generators a) u v
  exact (bracketDerivationDefect_eq_zero_coeff _ _ _ _).mp h n

theorem invariant_bracket {u v : Cochain} (hu : u ∈ relativeInvariants)
    (hv : v ∈ relativeInvariants) (n : ℕ) : BC.bracket u v n ∈ relativeInvariants := by
  rw [mem_relativeInvariants_iff] at hu hv ⊢
  intro a
  rw [colorAction_bracket, hu a, hv a]
  simp

end KhanSL2
