module

public import KhanSL2.BGG.HarmonicEnergy
public import KhanSL2.BGG.FreeCEEnergyAugmentation
public import KhanSL2.BGG.TermResolutionEquivariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KhanSL2.BGG.TermResolution

/-- The constructed boundary preserves the original quotient energy grading,
including the prescribed triangular shift of each induced generator. -/
theorem boundary_mem_termPiece (p : ℕ) {n : ℤ} {u : Term (p+1)}
    (hu : u ∈ termPiece (p+1) n) : boundary p u ∈ termPiece p n := by
  apply (mem_termPiece_iff_harmonicEnergy p n _).mpr
  rw [embedding_boundary, PositiveTransfer.totalEnergyScale_differential,
    (mem_termPiece_iff_harmonicEnergy (p+1) n u).mp hu,
    LinearMap.map_smul_of_tower]

/-- Every full-current BGG differential preserves actual physical energy. -/
theorem differential_mem_termPiece (p : ℕ) {n : ℤ} {u : Term (p+1)}
    (hu : u ∈ termPiece (p+1) n) : differential p u ∈ termPiece p n :=
  boundary_mem_termPiece p hu

/-- The augmentation lands in the scalar degree-zero term: every other energy vanishes. -/
theorem augmentation_eq_zero_of_energy_ne_zero {n : ℤ} {u : Term 0}
    (hu : u ∈ termPiece 0 n) (hn : n ≠ 0) : augmentation u = 0 := by
  have he := (mem_termPiece_iff_harmonicEnergy 0 n u).mp hu
  have h := congrArg FreeCE.augmentation
    (PositiveTransfer.totalEnergyScale_incl (termHarmonicEmbedding 0 u))
  rw [FreeCE.augmentation_totalEnergyScale, he, LinearMap.map_smul_of_tower, map_smul] at h
  change augmentation u = (2 : ℂ)^n * augmentation u at h
  have hn' : (2 : ℂ)^n - 1 ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hpow
    apply hn
    apply energyEigenvalue_injective
    simpa only [zpow_zero] using hpow
  have hz : ((2 : ℂ)^n - 1) * augmentation u = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left hn'
/-- Exactness and energy compatibility hold together for the specified current-module maps. -/
theorem exact_graded_current_module_complex :
    (∀ p, Function.Exact (differential (p+1)) (differential p)) ∧
    Function.Exact (differential 0) augmentation ∧ Function.Surjective augmentation ∧
    (∀ p n u, u ∈ termPiece (p+1) n → differential p u ∈ termPiece p n) :=
  ⟨exact_differentials, exact_differential_augmentation, augmentation_surjective,
    fun p _ _ hu => differential_mem_termPiece p hu⟩

end KhanSL2.BGG.TermResolution
