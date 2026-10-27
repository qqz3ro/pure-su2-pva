module

public import KhanSL2.BCFullHamiltonianB0

@[expose] public section

/-! The cubic Hamiltonian zero mode equals the full CE differential everywhere. -/

noncomputable section

namespace KhanSL2

open LambdaBracket

private theorem fullDifferential_zeroMode_ghost (a : Fin 3) :
    fullDifferential (ghost a) =
      zeroMode FullBC.bracket omegaHamiltonian (ghost a) := by
  have h := FullBC.bracket_super_skew (3, 1, 1) (1, 0, 0)
    omegaHamiltonian (ghost a) omegaHamiltonian_mem (ghost_mem a)
  rw [bracket_ghost_omega] at h
  norm_num [koszulSign, LambdaPolynomial.skew_single] at h
  have hc := congrArg (fun p : LambdaPolynomial FullCochain => p 0) h
  simpa [ghost] using hc.symm

private theorem fullDifferential_zeroMode_b0 (a : Fin 3) :
    fullDifferential (fullGenerator (.inr (.b 0 a))) =
      zeroMode FullBC.bracket omegaHamiltonian (fullGenerator (.inr (.b 0 a))) := by
  have h := FullBC.bracket_super_skew (3, 1, 1) (1, 1, 1)
    omegaHamiltonian (fullGenerator (.inr (.b 0 a))) omegaHamiltonian_mem (b0_mem a)
  rw [bracket_b0_omega] at h
  norm_num [koszulSign, LambdaPolynomial.skew_single] at h
  have hc := congrArg (fun p : LambdaPolynomial FullCochain => p 0) h
  simpa using hc.symm

private theorem fullDifferential_zeroMode_next (m : FullMode)
    (h : fullDifferential (fullGenerator m) =
      zeroMode FullBC.bracket omegaHamiltonian (fullGenerator m)) :
    fullDifferential (fullGenerator m.next) =
      zeroMode FullBC.bracket omegaHamiltonian (fullGenerator m.next) := by
  have ht := congrArg fullTranslation h
  have hz : zeroMode FullBC.bracket omegaHamiltonian (fullTranslation (fullGenerator m)) =
      fullTranslation (zeroMode FullBC.bracket omegaHamiltonian (fullGenerator m)) :=
    zeroMode_translation full_isPVA omegaHamiltonian (fullGenerator m)
  rw [← fullDifferential_fullTranslation, ← hz] at ht
  rw [fullTranslation_generator, fullTranslationGenerator] at ht
  simp only [map_smul] at ht
  have hr : (m.translationCoefficient : ℂ) ≠ 0 := by
    change ((m.order + 1 : ℕ) : ℂ) ≠ 0
    exact_mod_cast Nat.succ_ne_zero m.order
  have hh := congrArg (fun u : FullCochain => (m.translationCoefficient : ℂ)⁻¹ • u) ht
  simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul] using hh

theorem fullDifferential_zeroMode_generator (m : FullMode) :
    fullDifferential (fullGenerator m) =
      zeroMode FullBC.bracket omegaHamiltonian (fullGenerator m) := by
  cases m with
  | inl a => exact fullDifferential_zeroMode_ghost a
  | inr m =>
    cases m with
    | b j a =>
      induction j with
      | zero => exact fullDifferential_zeroMode_b0 a
      | succ j hj => exact fullDifferential_zeroMode_next (.inr (.b j a)) hj
    | c j a =>
      induction j with
      | zero =>
        exact fullDifferential_zeroMode_next (.inl a) (fullDifferential_zeroMode_ghost a)
      | succ j hj => exact fullDifferential_zeroMode_next (.inr (.c j a)) hj

theorem fullDifferential_eq_zeroMode (u : FullCochain) :
    fullDifferential u = zeroMode FullBC.bracket omegaHamiltonian u := by
  induction u using FiniteExterior.induction_on FullMode.code with
  | hzero => simp
  | hone =>
    change fullDifferential fullOne = zeroMode FullBC.bracket omegaHamiltonian fullOne
    simp
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu =>
    change fullDifferential (fullGenerator m * u) =
      zeroMode FullBC.bracket omegaHamiltonian (fullGenerator m * u)
    rw [fullDifferential_mul, fullParity_generator,
      fullDifferential_zeroMode_generator, hu]
    have h := zeroMode_mul full_isPVA omegaHamiltonian_mem (full_generator_mem m) u
    change zeroMode FullBC.bracket omegaHamiltonian (fullGenerator m * u) =
      zeroMode FullBC.bracket omegaHamiltonian (fullGenerator m) * u +
        koszulSign (3, 1, 1) (1, (m.bCount : ℤ), (m.weight : ℤ)) •
          (fullGenerator m * zeroMode FullBC.bracket omegaHamiltonian u) at h
    rw [h]
    simp [koszulSign]

theorem fullDifferential_eq_zeroMode_apply (u : FullCochain) :
    fullDifferential u = FullBC.bracket omegaHamiltonian u 0 :=
  fullDifferential_eq_zeroMode u

end KhanSL2
