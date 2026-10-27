module

public import KhanSL2.Factorization.BalancedShuffleNative

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
noncomputable section
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (M N : Type) [AddCommGroup M] [Module ℂ M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent ℂ M]
  [AddCommGroup N] [Module ℂ N] [LieRingModule Current N] [LieModule ℂ Current N]
  [CoefficientLinearCurrent ℂ N]

/-- The literal native/balanced square, packaged once as an isomorphism of arrows. -/
def nativeBalancedShuffleArrowIso :
    Arrow.mk (shuffleComplex M N) ≅ Arrow.mk (balancedShuffleComplex ℂ M N) :=
  Arrow.isoMk' _ _
    (nativeBalancedCoefficientComplexIso M N ≪≫
      (coefficientNativeComplexIso (BalancedCoefficients ℂ M N)).symm)
    (balancedNativeTensorIso M N).symm (by
      simpa only [Iso.trans_hom,Iso.symm_hom,Category.assoc,nativeBalancedCoefficientComplexIso]
        using balancedShuffleComplex_native M N)

/-- The actual native comparison inherits the quasi-isomorphism of its balanced form. -/
theorem nativeShuffle_quasiIso_of_balanced [QuasiIso (balancedShuffleComplex ℂ M N)] :
    QuasiIso (shuffleComplex M N) :=
  (quasiIso_iff_of_arrow_mk_iso (shuffleComplex M N) (balancedShuffleComplex ℂ M N)
    (nativeBalancedShuffleArrowIso M N)).mpr inferInstance

end KhanSL2.Factorization
