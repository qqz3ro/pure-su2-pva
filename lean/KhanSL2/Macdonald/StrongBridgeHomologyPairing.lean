module

public import KhanSL2.Macdonald.StrongBridgeTotalEvaluation
public import KhanSL2.Macdonald.StrongBridgeFreeAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The normalized actual homology model is characterized by the original
bilinear pairing with every free harmonic representative. -/
noncomputable section
namespace KhanSL2.Macdonald
open Factorization BGGBridge

@[simp] theorem strongFreeCoordinateEquiv_symm_single_val (b : strongFreeIndices) :
    (strongFreeCoordinateEquiv.symm (Finsupp.single b 1)).val =
      StrongMacdonald.mono b.val.1 b.val.2 := by
  have hm : StrongMacdonald.mono b.val.1 b.val.2 ∈ strongFree := by
    change StrongMacdonald.projFull (StrongMacdonald.mono b.val.1 b.val.2) = _
    rw [StrongMacdonald.projFull, StrongMacdonald.proj_mono]
    exact if_pos b.property
  let u : strongFree := ⟨_,hm⟩
  have he : strongFreeCoordinateEquiv u = Finsupp.single b 1 := by
    ext c
    rw [strongFreeCoordinateEquiv_apply]
    simp only [u, StrongMacdonald.coefW_mono, Finsupp.single_apply]
    have hi : (b.val.1 = c.val.1 ∧ b.val.2 = c.val.2) ↔ b = c := by
      rw [← Prod.ext_iff, Subtype.ext_iff]
    simp only [hi]
  exact congrArg Subtype.val (strongFreeCoordinateEquiv.symm_apply_eq.mpr he.symm)

/-- Factorial normalization makes the free-model pairing exactly coordinate evaluation. -/
theorem strongTotalHomologyFreeEquiv_pairing_mono
    (v : TotalHomology SymmetricCoefficients) (b : strongFreeIndices) :
    pairing (strongModel (StrongMacdonald.mono b.val.1 b.val.2))
      (strongModel (strongTotalHomologyFreeEquiv v).val) =
        strongTotalHomologyCoordinateEquiv v b := by
  rw [strongModel_mono, pairing_basis_left]
  rw [basis_repr_strongModel (strongTotalHomologyFreeEquiv v).val b.val.1 b.val.2]
  rw [← strongFreeCoordinateEquiv_apply (strongTotalHomologyFreeEquiv v) b,
    strongTotalHomologyFreeEquiv_coordinate]
  unfold strongFreeFactorial
  rw [← mul_assoc, mul_inv_cancel₀
    (Nat.cast_ne_zero.mpr (exponentFactorial_ne_zero _)), one_mul]

/-- The full finite-support model evaluates exactly the specified Gmap cochain
on any genuine relative cycle. -/
theorem strongTotalHomologyFreeEquiv_pairing_cycle
    (u : strongFree) (z : RawChains SymmetricCoefficients)
    (hz : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk z) = 0) :
    pairing (strongModel u.val)
      (strongModel (strongTotalHomologyFreeEquiv (totalSymmetricCycleClass z hz)).val) =
        pairing (strongModel (StrongMacdonald.Gmap u.val)) (chainModel z) := by
  obtain ⟨x,rfl⟩ := strongFreeCoordinateEquiv.symm.surjective u
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Submodule.coe_add, LinearMap.add_apply, hx, hy]
  | single b c =>
    have he : Finsupp.single b c = c • Finsupp.single b (1 : ℂ) := by simp
    rw [he]
    simp only [map_smul, Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul,
      strongFreeCoordinateEquiv_symm_single_val]
    rw [strongTotalHomologyFreeEquiv_pairing_mono,
      strongTotalHomologyCoordinateEquiv_evaluate]

end KhanSL2.Macdonald
