module

public import KhanSL2.BGG.PositiveTransferEnergy
public import KhanSL2.BGG.HarmonicTensorTerms

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG

/-- The intrinsic positive-tensor energy pieces are exactly the dilation eigenspaces. -/
theorem positiveTensorPiece_eq_eigenspace (p : ℕ) (n : ℤ) :
    positiveTensorPiece p n = Module.End.eigenspace (positiveTensorDilation p) ((2 : ℂ)^n) := by
  have h := ((Module.End.eigenspaces_iSupIndep (positiveTensorDilation p)).comp
    energyEigenvalue_injective).le_iff_eq_of_iSup_eq_top (iSup_positiveTensorPiece_eq_top p)
  exact congrFun (h.mp (positiveTensorPiece_le_eigenspace p)) n

theorem generatorEnergy_eq_triangular (p : ℕ) : generatorEnergy p = triangular p := by
  have h := two_mul_triangular p
  unfold generatorEnergy
  omega

/-- The chosen coefficient realization has exactly the prescribed triangular energy. -/
theorem standardHarmonicEmbedding_energyScale (p : ℕ) (v : Coefficient p) :
    PositiveCE.harmonicEnergyScale (PositiveCE.standardHarmonicEmbedding p v) =
      ((2 : ℂ)^(generatorEnergy p : ℤ)) • PositiveCE.standardHarmonicEmbedding p v := by
  apply Subtype.ext
  simpa only [PositiveCE.harmonicEnergyScale_coe, Submodule.coe_smul, zpow_natCast, generatorEnergy_eq_triangular] using
    PositiveCE.energyScale_of_piece (PositiveCE.standardHarmonicEmbedding_mem_piece p v)

/-- The PBW harmonic identification intertwines the actual shifted dilation. -/
theorem harmonicTensorEmbedding_energyScale (p : ℕ)
    (u : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    PositiveTransfer.totalEnergyScale (harmonicTensorEmbedding p u) =
      harmonicTensorEmbedding p (positiveTensorDilation p u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a v =>
    simp only [harmonicTensorEmbedding_tmul, PositiveTransfer.totalEnergyScale_tmul,
      standardHarmonicEmbedding_energyScale, TensorProduct.tmul_smul,
      positiveTensorDilation, LinearMap.smul_apply, TensorProduct.map_tmul,
      AlgHom.toLinearMap_apply, LinearMap.id_apply, LinearMap.map_smul_of_tower]

/-- Intrinsic PBW degree is detected by total physical-energy dilation after harmonic inclusion. -/
theorem mem_positiveTensorPiece_iff_harmonicEnergy (p : ℕ) (n : ℤ)
    (u : PositiveEnveloping ⊗[ℂ] Coefficient p) :
    u ∈ positiveTensorPiece p n ↔
      PositiveTransfer.totalEnergyScale (harmonicTensorEmbedding p u) =
        (2 : ℂ)^n • harmonicTensorEmbedding p u := by
  rw [positiveTensorPiece_eq_eigenspace, Module.End.mem_eigenspace_iff,
    harmonicTensorEmbedding_energyScale, ← LinearMap.map_smul_of_tower]
  exact (show Function.LeftInverse (harmonicTensorProjection p) (harmonicTensorEmbedding p)
    from harmonicTensorProjection_embedding p).injective.eq_iff.symm

/-- The original quotient energy grading is precisely the physical energy of its actual harmonic realization. -/
theorem mem_termPiece_iff_harmonicEnergy (p : ℕ) (n : ℤ) (u : Term p) :
    u ∈ termPiece p n ↔
      PositiveTransfer.totalEnergyScale (termHarmonicEmbedding p u) =
        (2 : ℂ)^n • termHarmonicEmbedding p u := by
  let v := (positiveTensorEquivTerm p).symm u
  have h := (positiveTensorEquivTerm_mem_iff p n v).trans
    (mem_positiveTensorPiece_iff_harmonicEnergy p n v)
  change u ∈ termPiece p n ↔
    PositiveTransfer.totalEnergyScale (harmonicTensorEmbedding p ((positiveTensorEquivTerm p).symm u)) =
      (2 : ℂ)^n • harmonicTensorEmbedding p ((positiveTensorEquivTerm p).symm u)
  simpa only [v, LinearEquiv.apply_symm_apply] using h

end KhanSL2.BGG
