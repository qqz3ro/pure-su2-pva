module

public import KhanSL2.Modules.CoefficientOperators
public import KhanSL2.Modules.ModeShifts

@[expose] public section

/-! # Coefficient power sums agree with the concrete mode-shift derivations -/

noncomputable section
open scoped TensorProduct

namespace KhanSL2.Modules

open Current LieChains

/-- The comparison on coefficient generators intertwines the specified shifts. -/
theorem raiseB_phiB (m : ℕ) (x : Cur) :
    raiseB m (phiB x) = phiB (coefficientShift m x) := by
  have h : (raiseB m).comp phiB = phiB.comp (coefficientShift m) := by
    apply curBasis.ext
    rintro ⟨j, a⟩
    simp [curBasis_apply', raiseBGenerator, Nat.add_comm]
  exact LinearMap.congr_fun h x

/-- Positive-current factors are untouched by coefficient power sums. -/
theorem raiseB_phiC (m : ℕ) (x : plus) : raiseB m (phiC x) = 0 := by
  have h : (raiseB m).comp phiC = 0 := by
    apply plusBasis.ext
    rintro ⟨j, a⟩
    simp [plusBasis_apply, raiseBGenerator]
  exact LinearMap.congr_fun h x

theorem raiseB_PhiC (m : ℕ) (u : ExteriorAlgebra ℂ plus) : raiseB m (PhiC u) = 0 := by
  induction u using CliffordAlgebra.left_induction with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]
  | ι_mul u x hu =>
    rw [map_mul, PhiC_ι, raiseB_mul, raiseB_phiC, hu, zero_mul, mul_zero, add_zero]

/-- The algebra comparison intertwines the full derivations on the coefficient algebra. -/
theorem PhiB_coefficientPower (m : ℕ) (v : NB) :
    PhiB (coefficientPower m v) = raiseB m (PhiB v) := by
  induction v using CliffordAlgebra.left_induction with
  | algebraMap r => simp [coefficientPower, Algebra.algebraMap_eq_smul_one]
  | add u v hu hv => simp only [map_add, hu, hv]
  | ι_mul u x hu =>
    simp only [coefficientPower, derivExt_ι_mul, map_add, map_mul, PhiB_ι,
      raiseB_mul, raiseB_phiB]
    rw [show PhiB (derivExt (coefficientShift m) u) = raiseB m (PhiB u) from hu]

/-- The genuine coefficient-chain operator is the concrete raising derivation. -/
theorem Phi_coefficientChainPower (m : ℕ) (ξ : GenChains) :
    Phi (coefficientChainPower m ξ) = raiseB m (Phi ξ) := by
  induction ξ using TensorProduct.induction_on with
  | zero => simp
  | tmul u v =>
    rw [coefficientChainPower_tmul, Phi_tmul, Phi_tmul, raiseB_mul,
      raiseB_PhiC, zero_mul, zero_add, PhiB_coefficientPower]
  | add ξ η hξ hη => simp only [map_add, hξ, hη]

end KhanSL2.Modules
