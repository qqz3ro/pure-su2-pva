module

public import KhanSL2.Macdonald.StrongBridgeHomologyShift
public import KhanSL2.Macdonald.StrongBridgeFreeRaising

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The normalized explicit homology equivalence intertwines the actual
power-sum action with the concrete weighted free raising derivation. -/
noncomputable section
namespace KhanSL2.Macdonald
open Factorization

/-- The original factorial pairing remains nondegenerate on the color-zero source. -/
theorem strongFree_pairing_ext {u v : strongFree}
    (h : ∀ t : strongFree, pairing (strongModel t.val) (strongModel u.val) =
      pairing (strongModel t.val) (strongModel v.val)) : u = v := by
  apply strongFreeCoordinateEquiv.injective
  ext b
  have hb := h (strongFreeCoordinateEquiv.symm (Finsupp.single b 1))
  rw [strongFreeCoordinateEquiv_symm_single_val,strongModel_mono,
    pairing_basis_left,pairing_basis_left,
    basis_repr_strongModel u.val b.val.1 b.val.2,
    basis_repr_strongModel v.val b.val.1 b.val.2] at hb
  have hn : (exponentFactorial (strongExponentEquiv b.val.1) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (exponentFactorial_ne_zero _)
  simpa only [strongFreeCoordinateEquiv_apply] using mul_left_cancel₀ hn hb

/-- The actual coefficient action and the explicit free action agree under H. -/
theorem strongTotalHomologyFreeEquiv_shift (m : ℕ)
    (h : TotalHomology SymmetricCoefficients) :
    strongTotalHomologyFreeEquiv (totalSymmetricShift m h) =
      strongFreeRaiseEnd m (strongTotalHomologyFreeEquiv h) := by
  apply strongFree_pairing_ext
  intro u
  calc
    pairing (strongModel u.val)
        (strongModel (strongTotalHomologyFreeEquiv (totalSymmetricShift m h)).val) =
      pairing (strongModel (strongFreeLowerEnd m u).val)
        (strongModel (strongTotalHomologyFreeEquiv h).val) :=
          strongTotalHomologyFreeEquiv_shift_pairing m u h
    _ = pairing (strongModel (strongTotalHomologyFreeEquiv h).val)
        (strongModel (strongFreeLowerEnd m u).val) := pairing_symm _ _
    _ = pairing (strongModel (strongFreeRaiseEnd m (strongTotalHomologyFreeEquiv h)).val)
        (strongModel u.val) := (strongFreeRaiseEnd_adjoint m _ u).symm
    _ = _ := pairing_symm _ _

end KhanSL2.Macdonald
