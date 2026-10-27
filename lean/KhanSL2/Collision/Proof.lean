module

public import KhanSL2.Factorization.FiniteBGGChartFactorization
public import KhanSL2.SymmetricFamily.SymmetricTensorShuffleProved

@[expose] public section
noncomputable section
namespace KhanSL2.Collision

/-- The factorization of the original K-modules is proved on every etale
coprime chart, with the original factor-coefficient scalar actions. -/
theorem kFactor (B : ℕ) : KFactor B :=
  kFactor_of_symmetricTensorShuffle SymmetricFamily.symmetricTensorShuffle B

end KhanSL2.Collision
