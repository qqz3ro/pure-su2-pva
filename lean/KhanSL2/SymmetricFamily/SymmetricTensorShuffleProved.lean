module

public import KhanSL2.SymmetricFamily.SymmetricChartHomology
public import KhanSL2.SymmetricFamily.SymmetricTensorShuffle

@[expose] public section
noncomputable section
namespace KhanSL2.SymmetricFamily

/-- The actual relative CE shuffle is a quasi-isomorphism for any two prescribed
symmetric local tensor families with distinct, disjoint supports. -/
theorem symmetricTensorShuffle : Factorization.SymmetricTensorShuffle :=
  symmetricTensorShuffle_of_universalCharts
    (fun r s => symmetricChartComplex_quasiIso (productChartData r s))

end KhanSL2.SymmetricFamily
