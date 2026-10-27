module

public import KhanSL2.Modules.CoefficientComparison
public import KhanSL2.Modules.CoefficientHomology
public import KhanSL2.Modules.PolynomialComparison

@[expose] public section

/-! # Quotient representatives for the coefficient action and cohomology pairing -/

noncomputable section
namespace KhanSL2.Modules

open Current LieChains

/-- The specified shift of a lifted relative cycle. -/
def coefficientLiftedCycle (m p B : ℕ) (S : ℤ)
    (ξ : genCycles (kDegree p B S)) : genCycles (kDegree p B (S + m)) :=
  ⟨coefficientChainPower m ξ,
    coefficientChainPower_mem_piece m p B S ξ.property.1, by
      change LieChains.boundary NB (coefficientChainPower m ξ) ∈ genRelations
      rw [boundary_coefficientChainPower]
      exact coefficientChainPower_mem_relations m ξ.property.2⟩

/-- The homology operator is represented by the actual shifted CE cycle. -/
theorem coefficientKPower_cyclesToRelHomology (m p B : ℕ) (S : ℤ)
    (ξ : genCycles (kDegree p B S)) :
    coefficientKPower m p B S (cyclesToRelHomology (kDegree p B S) ξ) =
      cyclesToRelHomology (kDegree p B (S + m)) (coefficientLiftedCycle m p B S ξ) := rfl

/-- The comparison to the quotient-complex definition sends a lifted cycle to its class. -/
theorem relHomologyEquivComplex_mk (d : Degree) (ξ : genCycles d) :
    relHomologyEquivComplex d (Submodule.Quotient.mk ξ) = cyclesToRelHomology d ξ := rfl

/-- The dictionary uses the same concrete representative `Phi ξ`. -/
theorem kChainEquiv_cyclesToRelHomology (p B : ℕ) (S : ℤ)
    (ξ : genCycles (kDegree p B S)) :
    kChainEquiv p B S (cyclesToRelHomology (kDegree p B S) ξ) =
      Submodule.Quotient.mk (cyclesEquiv (kDegree p B S) ξ) := by
  exact congrArg (relHomologyEquiv (kDegree p B S))
    ((relHomologyEquivComplex (kDegree p B S)).symm_apply_apply (Submodule.Quotient.mk ξ))

/-- Pairing with an actual homology representative is the original coefficient pairing. -/
theorem cohomologyToDual_kCycle (p B : ℕ) (S : ℤ) (u : Cochain) (hu : u ∈ relativeCycles)
    (ξ : genCycles (kDegree p B S)) :
    cohomologyToDual (kDegree p B S) (classOf u hu)
      (kChainEquiv p B S (cyclesToRelHomology (kDegree p B S) ξ)) =
      pairing u (Phi ξ) := by
  exact (congrArg (cohomologyToDual (kDegree p B S) (classOf u hu))
    (kChainEquiv_cyclesToRelHomology p B S ξ)).trans
    (cohomologyToDual_classOf (kDegree p B S) u hu (cyclesEquiv (kDegree p B S) ξ))

/-- Compatibility of the actual homology action with the concrete raising derivation. -/
theorem cohomologyToDual_coefficientKPower (m p B : ℕ) (S : ℤ)
    (u : Cochain) (hu : u ∈ relativeCycles) (ξ : genCycles (kDegree p B S)) :
    cohomologyToDual (kDegree p B (S + m)) (classOf u hu)
      (kChainEquiv p B (S + m)
        (coefficientKPower m p B S (cyclesToRelHomology (kDegree p B S) ξ))) =
      pairing u (raiseB m (Phi ξ)) := by
  exact (cohomologyToDual_kCycle p B (S + m) u hu
    (coefficientLiftedCycle m p B S ξ)).trans
    (congrArg (pairing u) (Phi_coefficientChainPower m ξ))

end KhanSL2.Modules
