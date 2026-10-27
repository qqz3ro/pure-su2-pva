module

public import KhanSL2.Macdonald.TensorPairing
public import KhanSL2.Factorization.ShuffleParityDegree

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The exterior coefficient pairing is dual to the actual signed shuffle.
This retains the signs used by the relative-chain comparison. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Macdonald
open FiniteExterior BGGBridge

/-- The canonical exterior shuffle in the actual finite-coordinate model. -/
def exteriorCoproduct : Exterior →ₗ[ℂ] Exterior ⊗[ℂ] Exterior :=
  (TensorProduct.map exteriorEquiv.toLinearMap exteriorEquiv.toLinearMap).comp
    ((Factorization.ExteriorShuffle.shuffle Current.plus).comp exteriorEquiv.symm.toLinearMap)

def exteriorCreate (m : Mode) : Module.End ℂ (Exterior ⊗[ℂ] Exterior) :=
  (LinearMap.mulLeft ℂ (FiniteExterior.generator m)).rTensor Exterior +
    TensorProduct.map parityLinear (LinearMap.mulLeft ℂ (FiniteExterior.generator m))

@[simp] theorem exteriorCreate_tmul (m : Mode) (u v : Exterior) :
    exteriorCreate m (u ⊗ₜ[ℂ] v) =
      (FiniteExterior.generator m * u) ⊗ₜ[ℂ] v + parityLinear u ⊗ₜ[ℂ] (FiniteExterior.generator m * v) := rfl

@[simp] theorem exteriorCoproduct_one :
    exteriorCoproduct 1 = (1 : Exterior) ⊗ₜ[ℂ] 1 := by
  simp [exteriorCoproduct]

@[simp] theorem exteriorEquiv_ι_mode (m : Mode) :
    exteriorEquiv (ExteriorAlgebra.ι ℂ (plusModeBasis m)) = FiniteExterior.generator m :=
  toE_ι_basis m

theorem exteriorCoproduct_generator_mul (m : Mode) (u : Exterior) :
    exteriorCoproduct (FiniteExterior.generator m * u) = exteriorCreate m (exteriorCoproduct u) := by
  have ht (t : Factorization.ExteriorShuffle.Tensor Current.plus) :
      TensorProduct.map exteriorEquiv.toLinearMap exteriorEquiv.toLinearMap
        (Factorization.ExteriorShuffle.create Current.plus (plusModeBasis m) t) =
      exteriorCreate m (TensorProduct.map exteriorEquiv.toLinearMap exteriorEquiv.toLinearMap t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add t v ht hv => simp only [map_add, ht, hv]
    | tmul a b =>
      simp only [Factorization.ExteriorShuffle.create_tmul, map_add, TensorProduct.map_tmul,
        AlgEquiv.toLinearMap_apply, map_mul, exteriorEquiv_ι_mode,
        Factorization.exteriorEquiv_parity, exteriorCreate_tmul]
  obtain ⟨v,rfl⟩ := exteriorEquiv.surjective u
  rw [show FiniteExterior.generator m = exteriorEquiv (ExteriorAlgebra.ι ℂ (plusModeBasis m)) from
    (toE_ι_basis m).symm, ← map_mul]
  simp only [exteriorCoproduct, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.symm_apply_apply, Factorization.ExteriorShuffle.shuffle_ι_mul]
  exact ht _

def exteriorTensorPairing (p q : Exterior) : Exterior ⊗[ℂ] Exterior →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((coefficientPairing p).smulRight (coefficientPairing q))

@[simp] theorem exteriorTensorPairing_tmul (p q r s : Exterior) :
    exteriorTensorPairing p q (r ⊗ₜ[ℂ] s) = coefficientPairing p r * coefficientPairing q s := rfl

theorem coefficientPairing_parity (p q : Exterior) :
    coefficientPairing (parityLinear p) q = coefficientPairing p (parityLinear q) := by
  classical
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p r hp hr => simp only [map_add, LinearMap.add_apply, hp, hr]
  | single s a =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add q r hq hr => simp only [map_add, hq, hr]
    | single t b =>
      by_cases h : s = t
      · subst t
        simp [mul_comm, mul_left_comm]
      · simp [Finsupp.single_apply, h, Ne.symm h]

@[simp] theorem coefficientPairing_exterior_one_one :
    coefficientPairing (1 : Exterior) 1 = 1 := by
  change coefficientPairing (FiniteExterior.monomial ∅) (FiniteExterior.monomial ∅) = 1
  simp [FiniteExterior.monomial]

theorem coefficientPairing_positiveContract (m : Mode) (u v : Exterior) :
    coefficientPairing (BGG.PositiveCE.contract m u) v =
      coefficientPairing u (FiniteExterior.generator m * v) :=
  coefficientPairing_contraction m u v

theorem coefficientPairing_mul_one (p q : Exterior) :
    coefficientPairing (p*q) 1 = coefficientPairing p 1 * coefficientPairing q 1 := by
  refine FiniteExterior.induction_on BGG.PositiveCE.Mode.code
    (P := fun p => coefficientPairing (p*q) 1 = coefficientPairing p 1 * coefficientPairing q 1)
    ?_ ?_ ?_ ?_ ?_ p
  · simp
  · simp [show (FiniteExterior.monomial (∅ : Finset Mode) : Exterior) = 1 from rfl]
  · intro p r hp hr
    simp only [add_mul, map_add, LinearMap.add_apply, hp, hr]
  · intro c p hp
    simp only [smul_mul_assoc, map_smul, LinearMap.smul_apply, hp, smul_eq_mul]
    ring
  · intro m p _hp
    change coefficientPairing ((FiniteExterior.generator m * p)*q) 1 =
      coefficientPairing (FiniteExterior.generator m*p) 1 * coefficientPairing q 1
    rw [mul_assoc, coefficientPairing_generator_mul, coefficientPairing_generator_mul]
    simp [contraction_monomial, show (1 : Exterior) = FiniteExterior.monomial ∅ from rfl]

theorem exteriorTensorPairing_create (m : Mode) (p q : Exterior) (t : Exterior ⊗[ℂ] Exterior) :
    exteriorTensorPairing p q (exteriorCreate m t) =
      exteriorTensorPairing (BGG.PositiveCE.contract m p) q t +
        exteriorTensorPairing (parityLinear p) (BGG.PositiveCE.contract m q) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add t v ht hv =>
    simp only [map_add, ht, hv]
    abel
  | tmul r s =>
    simp only [exteriorCreate_tmul, map_add, exteriorTensorPairing_tmul,
      coefficientPairing_positiveContract, coefficientPairing_parity]

/-- Wedge multiplication is exactly transpose to the signed shuffle coproduct. -/
theorem coefficientPairing_mul_coproduct (p q r : Exterior) :
    coefficientPairing (p*q) r = exteriorTensorPairing p q (exteriorCoproduct r) := by
  have h (r : Exterior) : ∀ p q : Exterior,
      coefficientPairing (p*q) r = exteriorTensorPairing p q (exteriorCoproduct r) := by
    refine FiniteExterior.induction_on BGG.PositiveCE.Mode.code (P := fun r => ∀ p q,
      coefficientPairing (p*q) r = exteriorTensorPairing p q (exteriorCoproduct r))
      ?_ ?_ ?_ ?_ ?_ r
    · intro p q; simp
    · intro p q
      change coefficientPairing (p*q) 1 = exteriorTensorPairing p q (exteriorCoproduct 1)
      rw [exteriorCoproduct_one, exteriorTensorPairing_tmul, coefficientPairing_mul_one]
    · intro r s hr hs p q
      simp only [map_add, hr, hs]
    · intro c r hr p q
      simp only [map_smul, hr]
    · intro m r hr p q
      change coefficientPairing (p*q) (FiniteExterior.generator m*r) =
        exteriorTensorPairing p q (exteriorCoproduct (FiniteExterior.generator m*r))
      rw [← coefficientPairing_contraction, exteriorCoproduct_generator_mul,
        exteriorTensorPairing_create]
      have hc : BGG.PositiveCE.contract m (p*q) =
          BGG.PositiveCE.contract m p * q + parityLinear p * BGG.PositiveCE.contract m q :=
        contraction_wedge BGG.PositiveCE.Mode.code BGG.PositiveCE.Mode.code_injective m p q
      change coefficientPairing (BGG.PositiveCE.contract m (p*q)) r = _
      rw [hc, map_add, LinearMap.add_apply, hr, hr]
  exact h r p q

end KhanSL2.Macdonald
