module

public import KhanSL2.BGG.PositiveBoundaryEquivariance

@[expose] public section

/-! Equivariance of contraction, with the actual compact-color matrix. -/
noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PositiveCE

/-- A color derivation commutes with contraction up to the natural dual color action. -/
theorem colorAction_contract (a : Fin 3) (m : Mode) (u : Cochain) :
    colorAction a (contract m u) = contract m (colorAction a u) +
      ∑ c : Fin 3, epsilon a m.color c • contract (⟨m.index,c⟩ : Mode) u := by
  have hc (k : Mode) (w z : Cochain) : coefficientPairing (contract k w) z =
      coefficientPairing w (FiniteExterior.generator k * z) :=
    coefficientPairing_contraction (α := Mode) k w z
  apply sub_eq_zero.mp
  apply coefficientPairing_left_nondegenerate
  intro v
  have hsum : coefficientPairing
      (∑ c : Fin 3, epsilon a m.color c • contract (⟨m.index,c⟩ : Mode) u) v =
      coefficientPairing u (colorAction a (FiniteExterior.generator m) * v) := by
    rw [colorAction_generator]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      Finset.sum_mul, smul_mul_assoc, hc]
  simp only [map_sub, LinearMap.sub_apply, map_add, LinearMap.add_apply]
  rw [colorAction_pairing, hc, hc, colorAction_pairing, hsum, colorAction_mul, map_add]
  ring

end KhanSL2.BGG.PositiveCE
