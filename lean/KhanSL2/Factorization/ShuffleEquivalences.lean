module

public import KhanSL2.Factorization.ShuffleRetracts

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Transfer the actual shuffle quasi-isomorphism along specified current-module equivalences. -/
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open BGG
variable {M N : Type}
  [AddCommGroup M] [Module ℂ M] [LieRingModule Current M] [LieModule ℂ Current M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
variable (T : Type) [AddCommGroup T] [Module ℂ T]
  [LieRingModule Current T] [LieModule ℂ Current T]

theorem shuffle_quasiIso_of_equiv_first (e : N ≃ₗ⁅ℂ,Current⁆ M)
    [QuasiIso (shuffleComplex M T)] : QuasiIso (shuffleComplex N T) := by
  apply shuffle_quasiIso_of_retract_first T e.toLieModuleHom e.symm.toLieModuleHom
  apply LinearMap.ext
  exact e.symm_apply_apply

theorem shuffle_quasiIso_of_equiv_second (e : N ≃ₗ⁅ℂ,Current⁆ M)
    [QuasiIso (shuffleComplex T M)] : QuasiIso (shuffleComplex T N) := by
  apply shuffle_quasiIso_of_retract_second T e.toLieModuleHom e.symm.toLieModuleHom
  apply LinearMap.ext
  exact e.symm_apply_apply

end KhanSL2.Factorization
