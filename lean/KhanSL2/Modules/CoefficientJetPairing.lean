module

public import KhanSL2.Modules.CoefficientPairing
public import KhanSL2.Modules.ModeShiftAdjoint
public import KhanSL2.Modules.ShiftWords

@[expose] public section

/-! # The actual coefficient action paired with prescribed source jet words -/

noncomputable section
namespace KhanSL2.Modules
open SourceDual Current
set_option maxHeartbeats 2000000

/-- Evaluate the source functional on the concrete cycle representing a homology class. -/
theorem sourceFunctional_kCycle (p B : ℕ) (spin : ℤ)
    (ξ : genCycles (kDegree p B spin)) {r s : ℕ} (d : Variables r s →₀ ℕ) :
    sourceFunctional p B spin (cyclesToRelHomology (kDegree p B spin) ξ)
      (exponentMonomial d) = pairing (exponentRepresentative d) (Phi ξ) := by
  rw [sourceFunctional_apply, phi_exponentMonomial, cohomologyToDual_kCycle]

/-- A coefficient shift lowers each source jet with its actual falling-factorial coefficient. -/
theorem sourceFunctional_coefficientKPower_cycle (m p B : ℕ) (spin : ℤ)
    (ξ : genCycles (kDegree p B spin)) {r s : ℕ} (d : Variables r s →₀ ℕ) :
    sourceFunctional p B (spin+m)
      (coefficientKPower m p B spin (cyclesToRelHomology (kDegree p B spin) ξ))
      (exponentMonomial d) =
    ∑ i, (wordRootWeight i * ((d i).descFactorial m : ℂ)) *
      sourceFunctional p B spin (cyclesToRelHomology (kDegree p B spin) ξ)
        (exponentMonomial (d - Finsupp.single i m)) := by
  classical
  refine (congrArg (fun a => cohomologyToDual (kDegree p B (spin+m)) a
    (kChainEquiv p B (spin+m)
      (coefficientKPower m p B spin (cyclesToRelHomology (kDegree p B spin) ξ))))
    (phi_exponentMonomial d)).trans ?_
  refine (cohomologyToDual_coefficientKPower m p B spin
    (exponentRepresentative d) (exponentRepresentative_mem_cycles d) ξ).trans ?_
  rw [pairing_raiseB, lowerB_exponentRepresentative]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun c : ℂ => (wordRootWeight i * ((d i).descFactorial m : ℂ)) * c)
    (sourceFunctional_kCycle p B spin ξ (d - Finsupp.single i m)).symm

/-- Compatibility for arbitrary classes in the actual relative CE homology. -/
theorem sourceFunctional_coefficientKPower (m p B : ℕ) (spin : ℤ)
    (k : Current.K p B spin) {r s : ℕ} (d : Variables r s →₀ ℕ) :
    sourceFunctional p B (spin+m) (coefficientKPower m p B spin k)
      (exponentMonomial d) =
    ∑ i, (wordRootWeight i * ((d i).descFactorial m : ℂ)) *
      sourceFunctional p B spin k (exponentMonomial (d - Finsupp.single i m)) := by
  obtain ⟨ξ, hξ⟩ := cyclesToRelHomology_surjective (kDegree p B spin) k
  rw [← hξ]
  exact sourceFunctional_coefficientKPower_cycle m p B spin ξ d

end KhanSL2.Modules
