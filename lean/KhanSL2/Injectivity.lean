module

public import KhanSL2.Injectivity.SelectedCycles
public import KhanSL2.Injectivity.TaylorChainComparison
public import KhanSL2.Injectivity.TaylorRealization
public import KhanSL2.Injectivity.GradedSeparation

@[expose] public section

/-! Injectivity of the existing, explicitly defined canonical map. -/

noncomputable section

namespace KhanSL2

/-- The canonical map is injective. The proof constructs closed Cartan chains
whose functionals separate each finite source sector, then uses the actual
source and cohomology gradings to separate arbitrary finite sums. -/
theorem phi_injective : Function.Injective phi := by
  apply Injectivity.phi_injective_of_taylor_realization
  intro r s N ell
  apply SourceDual.taylor_realization_of_nonzero_cycle_multiples r s N phi ?_ ell
  intro e p hp
  refine ⟨Injectivity.descendCartanFunctional
      (FiniteExterior.coefficientPairing (Injectivity.Cartan.selectedCycleChain r s e p))
      (Injectivity.Cartan.selectedCycleChain_closed r s e p),
    (-2 : ℂ) ^ s * Injectivity.Cartan.selectedCycleScalar r s,
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Injectivity.Cartan.selectedCycleScalar_ne_zero r s), ?_⟩
  rw [Injectivity.taylor_descended_chainPolynomial,
    Injectivity.Cartan.chainPolynomial_selectedCycle r s e p hp, map_smul, smul_smul]

end KhanSL2
