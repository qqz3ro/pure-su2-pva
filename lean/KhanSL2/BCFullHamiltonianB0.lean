module

public import KhanSL2.BCFullHamiltonian

@[expose] public section

/-! The cubic Hamiltonian on the three zeroth `b` modes. -/

noncomputable section

namespace KhanSL2

open LambdaPolynomial

theorem bracket_b0_omega (d : Fin 3) :
    FullBC.bracket (fullGenerator (.inr (.b 0 d))) omegaHamiltonian =
      Finsupp.single 0 (fullDifferentialGenerator (.inr (.b 0 d))) := by
  simp only [omegaHamiltonian, map_smul, map_sum]
  simp_rw [bracket_generator_cubic]
  have hcomm (a b : Fin 3) :
      fullGenerator (.inr (.b 0 a)) * ghost b =
        -(ghost b * fullGenerator (.inr (.b 0 a))) :=
    fullGenerator_anticomm (.inr (.b 0 a)) (.inl b)
  fin_cases d <;> apply Finsupp.ext
  all_goals intro n
  all_goals
    simp only [Finsupp.smul_apply, Finsupp.sum_apply, Finsupp.add_apply,
      Finsupp.sub_apply, mulRight_apply, mulLeft_apply, fullData_mul_apply,
      bracket_b0_b0, bracket_b0_ghost, Finsupp.zero_apply]
  all_goals
    by_cases hn : n = 0
    · subst n
      norm_num [Fin.sum_univ_three, epsilon, fullDifferentialGenerator,
        colorGenerator, Mode.color, Mode.recolor, hcomm,
        show fullOne = (1 : FullCochain) from rfl, smul_mul_assoc, mul_smul_comm]
      module
    · simp [Finsupp.single_apply, hn, eq_comm]

end KhanSL2
