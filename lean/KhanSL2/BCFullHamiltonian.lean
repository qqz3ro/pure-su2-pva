module

public import KhanSL2.BCFullPVA
public import KhanSL2.BCFullTranslation
public import KhanSL2.BCHamiltonianCalculus

@[expose] public section

/-! Identification of the full CE differential with its cubic Hamiltonian. -/

noncomputable section

namespace KhanSL2

open LambdaPolynomial

theorem ghost_mem (a : Fin 3) : ghost a ∈ fullPiece (1, 0, 0) := by
  exact full_generator_mem (.inl a)

theorem b0_mem (a : Fin 3) :
    fullGenerator (.inr (.b 0 a)) ∈ fullPiece (1, 1, 1) := by
  exact full_generator_mem (.inr (.b 0 a))

theorem b0_ghost_mem (a b : Fin 3) :
    fullGenerator (.inr (.b 0 a)) * ghost b ∈ fullPiece (2, 1, 1) := by
  exact full_wedge_mem (b0_mem a) (ghost_mem b)

theorem omegaHamiltonian_mem : omegaHamiltonian ∈ fullPiece (3, 1, 1) := by
  apply (fullPiece _).smul_mem
  apply (fullPiece _).sum_mem
  intro a _
  apply (fullPiece _).sum_mem
  intro b _
  apply (fullPiece _).sum_mem
  intro c _
  apply (fullPiece _).smul_mem
  exact full_wedge_mem (b0_ghost_mem a b) (ghost_mem c)

@[simp] theorem fullData_mul_apply (u v : FullCochain) : fullData.mul u v = u * v := rfl

theorem fullWedge_eq_mul (u v : FullCochain) : fullWedge u v = u * v := rfl

@[simp] theorem bracket_ghost_b0 (a b : Fin 3) :
    FullBC.bracket (ghost a) (fullGenerator (.inr (.b 0 b))) =
      Finsupp.single 0 ((if a = b then (1 : ℂ) else 0) • fullOne) := by
  simp [ghost, FullBC.kernel, FullBC.kernelCoefficient,
    FullMode.pairsWith, FullMode.order, Mode.order]

@[simp] theorem bracket_b0_ghost (a b : Fin 3) :
    FullBC.bracket (fullGenerator (.inr (.b 0 a))) (ghost b) =
      Finsupp.single 0 ((if a = b then (1 : ℂ) else 0) • fullOne) := by
  simp [ghost, FullBC.kernel, FullBC.kernelCoefficient,
    FullMode.pairsWith, FullMode.order, Mode.order]

@[simp] theorem bracket_ghost_ghost (a b : Fin 3) :
    FullBC.bracket (ghost a) (ghost b) = 0 := by
  simp [ghost, FullBC.kernel, FullBC.kernelCoefficient, FullMode.pairsWith]

@[simp] theorem bracket_b0_b0 (a b : Fin 3) :
    FullBC.bracket (fullGenerator (.inr (.b 0 a)))
      (fullGenerator (.inr (.b 0 b))) = 0 := by
  simp [FullBC.kernel, FullBC.kernelCoefficient, FullMode.pairsWith, Mode.pairsWith]

theorem bracket_generator_cubic (m : FullMode) (a b c : Fin 3) :
    FullBC.bracket (fullGenerator m)
      (fullGenerator (.inr (.b 0 a)) * ghost b * ghost c) =
    mulRight fullData
      (mulRight fullData (FullBC.bracket (fullGenerator m)
        (fullGenerator (.inr (.b 0 a)))) (ghost b) -
       mulLeft fullData (fullGenerator (.inr (.b 0 a)))
        (FullBC.bracket (fullGenerator m) (ghost b))) (ghost c) +
      mulLeft fullData (fullGenerator (.inr (.b 0 a)) * ghost b)
        (FullBC.bracket (fullGenerator m) (ghost c)) := by
  simp only [← fullWedge_eq_mul]
  rw [FullBC.bracket_super_leibniz _ (2, 1, 1) (fullGenerator m)
    (fullWedge (fullGenerator (.inr (.b 0 a))) (ghost b)) (ghost c)
    (full_generator_mem m) (b0_ghost_mem a b)]
  rw [FullBC.bracket_super_leibniz _ (1, 1, 1) (fullGenerator m)
    (fullGenerator (.inr (.b 0 a))) (ghost b)
    (full_generator_mem m) (b0_mem a)]
  simp [koszulSign, sub_eq_add_neg]

theorem bracket_ghost_omega (d : Fin 3) :
    FullBC.bracket (ghost d) omegaHamiltonian =
      Finsupp.single 0 (fullDifferentialGenerator (.inl d)) := by
  simp only [omegaHamiltonian, map_smul, map_sum]
  simp_rw [show ghost d = fullGenerator (.inl d) from rfl, bracket_generator_cubic]
  change -(1 / 2 : ℂ) •
      (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
        epsilon a b c •
          (mulRight fullData
            (mulRight fullData (FullBC.bracket (ghost d)
              (fullGenerator (.inr (.b 0 a)))) (ghost b) -
             mulLeft fullData (fullGenerator (.inr (.b 0 a)))
              (FullBC.bracket (ghost d) (ghost b))) (ghost c) +
            mulLeft fullData (fullGenerator (.inr (.b 0 a)) * ghost b)
              (FullBC.bracket (ghost d) (ghost c)))) = _
  simp only [bracket_ghost_b0, bracket_ghost_ghost, mulLeft_zero, sub_zero,
    mulRight_single, fullData_mul_apply, add_zero]
  simp only [show fullOne = (1 : FullCochain) from rfl, smul_mul_assoc, one_mul,
    ← Finsupp.smul_single, smul_smul]
  simp [fullDifferentialGenerator, eq_comm, Finsupp.single_sum, Finsupp.smul_single]
  apply Finsupp.ext
  intro n
  by_cases h : n = 0
  · subst n
    simp [Finset.sum_apply']
  · simp [Finsupp.single_apply, Finset.sum_apply', h, Ne.symm h]

end KhanSL2
