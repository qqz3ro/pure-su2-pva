module

public import KhanSL2.Macdonald.StrongBridgeHomologyPairing
public import KhanSL2.Macdonald.ShiftAdjoint
public import KhanSL2.Factorization.CoefficientMaps

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The original power-sum coefficient action on actual CE homology is exactly
transpose to the explicit weighted lowering action on free harmonic generators. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open Factorization BGGBridge

/-- Every actual total homology class has an actual raw relative cycle representative. -/
theorem totalSymmetricCycleClass_surjective (h : TotalHomology SymmetricCoefficients) :
    ∃ (z : RawChains SymmetricCoefficients)
      (hz : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk z) = 0),
      totalSymmetricCycleClass z hz = h := by
  obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective
    (PerfectDuality.pairBoundaries (Factorization.differential SymmetricCoefficients)
      (Factorization.differential SymmetricCoefficients)) h
  obtain ⟨z,hz⟩ := (relC SymmetricCoefficients).mkQ_surjective v.val
  have hv : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk z) = 0 := by
    rw [show Submodule.Quotient.mk z = v.val from hz]
    exact v.property
  refine ⟨z,hv,?_⟩
  change Submodule.Quotient.mk (⟨Submodule.Quotient.mk z,hv⟩ :
    LinearMap.ker (Factorization.differential SymmetricCoefficients)) = Submodule.Quotient.mk v
  congr 1
  exact Subtype.ext hz

/-- The actual coefficient raising operator is a map of the genuine square-zero pair. -/
def symmetricShiftPair (m : ℕ) :
    PerfectDuality.PairMap (Factorization.differential SymmetricCoefficients)
      (Factorization.differential SymmetricCoefficients)
      (Factorization.differential SymmetricCoefficients)
      (Factorization.differential SymmetricCoefficients) where
  left := Factorization.coefficientMap (symmetricCoefficientEnd m).toLinearMap
    (constantEquivariant_of_lieHom (symmetricCoefficientEnd m))
  middle := Factorization.coefficientMap (symmetricCoefficientEnd m).toLinearMap
    (constantEquivariant_of_lieHom (symmetricCoefficientEnd m))
  right := Factorization.coefficientMap (symmetricCoefficientEnd m).toLinearMap
    (constantEquivariant_of_lieHom (symmetricCoefficientEnd m))
  comm_in := LinearMap.ext (coefficientMap_differential (symmetricCoefficientEnd m))
  comm_out := LinearMap.ext (coefficientMap_differential (symmetricCoefficientEnd m))

/-- Power-sum action on the actual symmetric relative homology quotient. -/
def totalSymmetricShift (m : ℕ) : Module.End ℂ (TotalHomology SymmetricCoefficients) :=
  (symmetricShiftPair m).homologyMap (differential_comp_self SymmetricCoefficients)
    (differential_comp_self SymmetricCoefficients)

theorem symmetricShift_raw_cycle (m : ℕ) (z : RawChains SymmetricCoefficients)
    (hz : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk z) = 0) :
    Factorization.differential SymmetricCoefficients
      (Submodule.Quotient.mk (rawMap (symmetricCoefficientEnd m).toLinearMap z)) = 0 := by
  have h := LinearMap.mem_ker.mp ((symmetricShiftPair m).cyclesMap
    (⟨Submodule.Quotient.mk z,hz⟩ : LinearMap.ker
      (Factorization.differential SymmetricCoefficients))).property
  exact h

@[simp] theorem totalSymmetricShift_class (m : ℕ) (z : RawChains SymmetricCoefficients)
    (hz : Factorization.differential SymmetricCoefficients (Submodule.Quotient.mk z) = 0) :
    totalSymmetricShift m (totalSymmetricCycleClass z hz) =
      totalSymmetricCycleClass (rawMap (symmetricCoefficientEnd m).toLinearMap z)
        (symmetricShift_raw_cycle m z hz) := rfl

theorem chainModel_rawMap_symmetricShift (m : ℕ) (z : RawChains SymmetricCoefficients) :
    chainModel (rawMap (symmetricCoefficientEnd m).toLinearMap z) =
      chainCoefficientShift m (chainModel z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z t hz ht => simp only [map_add,hz,ht]
  | tmul ω p => rfl

/-- Exact power-sum adjunction for the actual homology model, retaining the
weight two of even generators and weight one of odd generators. -/
theorem strongTotalHomologyFreeEquiv_shift_pairing (m : ℕ)
    (u : strongFree) (h : TotalHomology SymmetricCoefficients) :
    pairing (strongModel u.val) (strongModel (strongTotalHomologyFreeEquiv
      (totalSymmetricShift m h)).val) =
      pairing (strongModel (strongFreeLowerEnd m u).val)
        (strongModel (strongTotalHomologyFreeEquiv h).val) := by
  obtain ⟨z,hz,rfl⟩ := totalSymmetricCycleClass_surjective h
  rw [totalSymmetricShift_class, strongTotalHomologyFreeEquiv_pairing_cycle,
    chainModel_rawMap_symmetricShift]
  rw [pairing_symm, coefficientShift_pairing, pairing_symm,
    coefficientShift_strongFree]
  exact (strongTotalHomologyFreeEquiv_pairing_cycle (strongFreeLowerEnd m u) z hz).symm

end KhanSL2.Macdonald
