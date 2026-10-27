module

public import KhanSL2.Injectivity.CartanContraction
public import KhanSL2.Injectivity.RootCurrent

/-! The upward Cartan current on chains is adjoint to the downward current
on cochains. This identifies the genuine CE boundary pairing. -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 600000

namespace KhanSL2.Injectivity.Cartan

def rootContract (k : ℕ) : Mode → Cochain →ₗ[ℂ] Cochain
  | .plus j => contract (.plus (j + k))
  | .minus j => -contract (.minus (j + k))
  | .neutral _ => 0
  | .cartan _ => 0

@[simp] theorem rootContract_one (k : ℕ) (m : Mode) : rootContract k m 1 = 0 := by
  cases m <;> simp [rootContract]

theorem rootContract_generator_mul (k : ℕ) (m n : Mode) (u : Cochain) :
    rootContract k m (generator n * u) =
      rootContract k m (generator n) * u - generator n * rootContract k m u := by
  cases m <;> simp only [rootContract, LinearMap.neg_apply, LinearMap.zero_apply,
    contract_mul, parity_generator, neg_mul, mul_neg, zero_mul, mul_zero, sub_zero] <;> module

theorem contract_loweringGenerator (k : ℕ) (m n : Mode) :
    contract m (loweringGenerator k n) = rootContract k m (generator n) := by
  cases m <;> cases n <;>
    simp only [loweringGenerator, rootContract, LinearMap.neg_apply,
      LinearMap.zero_apply, contract_generator, map_zero, map_neg,
      reduceCtorEq, ite_false, neg_zero]
  all_goals try { split <;> simp_all }
  all_goals split <;> split <;> simp_all <;> omega

theorem contract_lowering (k : ℕ) (m : Mode) (u : Cochain) :
    contract m (lowering k u) =
      lowering k (contract m u) + rootContract k m u := by
  refine FiniteExterior.induction_on Mode.code (P := fun u =>
    contract m (lowering k u) = lowering k (contract m u) + rootContract k m u)
      ?_ ?_ ?_ ?_ ?_ u
  · simp
  · change contract m (lowering k 1) = lowering k (contract m 1) + rootContract k m 1
    simp
  · intro u v hu hv
    simp only [map_add]
    rw [hu, hv]
    module
  · intro r u hu
    simp only [map_smul, hu, smul_add]
  · intro n u hu
    change contract m (lowering k (generator n * u)) =
      lowering k (contract m (generator n * u)) + rootContract k m (generator n * u)
    rw [lowering_mul, lowering_generator, map_add, contract_mul,
      loweringGenerator_odd, contract_loweringGenerator, contract_generator_mul,
      contract_generator_mul, map_sub, lowering_mul, lowering_generator,
      rootContract_generator_mul, hu]
    split <;> simp only [map_zero, neg_mul, mul_add, mul_sub] <;> module

theorem pairing_rootCurrentGenerator (k : ℕ) (m : Mode) (u v : Cochain) :
    FiniteExterior.coefficientPairing (rootCurrentGenerator k m * u) v =
      FiniteExterior.coefficientPairing u (rootContract k m v) := by
  cases m <;>
    simp [rootCurrentGenerator, rootContract, neg_mul,
      FiniteExterior.coefficientPairing_generator_mul, generator, contract] <;> rfl

theorem pairing_generator_mul (m : Mode) (u v : Cochain) :
    FiniteExterior.coefficientPairing (generator m * u) v =
      FiniteExterior.coefficientPairing u (contract m v) :=
  FiniteExterior.coefficientPairing_generator_mul m u v

theorem rootCurrentAction_adjoint (k : ℕ) (u v : Cochain) :
    FiniteExterior.coefficientPairing (rootCurrentAction k u) v =
      FiniteExterior.coefficientPairing u (lowering k v) := by
  refine FiniteExterior.induction_on Mode.code (P := fun u => ∀v,
    FiniteExterior.coefficientPairing (rootCurrentAction k u) v =
      FiniteExterior.coefficientPairing u (lowering k v)) ?_ ?_ ?_ ?_ ?_ u v
  · intro v
    simp
  · intro v
    change FiniteExterior.coefficientPairing (rootCurrentAction k 1) v =
      FiniteExterior.coefficientPairing 1 (lowering k v)
    rw [rootCurrentAction_one, map_zero, LinearMap.zero_apply]
    change 0 = FiniteExterior.coefficientPairing 1
      (FiniteExterior.extendDerivation Mode.code (loweringGenerator k) v)
    rw [← FiniteExterior.finiteDerivation_eq Mode.code (loweringGenerator k)
      (FiniteExterior.supportModes v) v (Finset.Subset.refl _),
      FiniteExterior.finiteDerivation_apply, map_sum]
    symm
    apply Finset.sum_eq_zero
    intro a _ha
    change FiniteExterior.coefficientPairing 1 (loweringGenerator k a * _) = 0
    cases a with
    | neutral j => simp [loweringGenerator]
    | cartan j => simp [loweringGenerator]
    | plus j =>
      by_cases h : k ≤ j <;> simp [loweringGenerator, h, generator]
    | minus j =>
      by_cases h : k ≤ j <;> simp [loweringGenerator, h, generator, neg_mul]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply, hu, hw]
  · intro r u hu v
    simp only [map_smul, LinearMap.smul_apply, hu]
  · intro m u hu v
    change FiniteExterior.coefficientPairing (rootCurrentAction k (generator m * u)) v =
      FiniteExterior.coefficientPairing (generator m * u) (lowering k v)
    rw [rootCurrentAction_mul, rootCurrentAction_generator, map_add, LinearMap.add_apply,
      pairing_rootCurrentGenerator]
    rw [pairing_generator_mul, pairing_generator_mul]
    rw [hu, contract_lowering, map_add, add_comm]

theorem pairing_cartan_q (i : ℕ) (c u : Cochain) :
    FiniteExterior.coefficientPairing (generator (.cartan i) * c) (q u) +
      FiniteExterior.coefficientPairing c (q (contract (.cartan i) u)) =
        -FiniteExterior.coefficientPairing (rootCurrentAction (i + 1) c) u := by
  have h := congrArg (FiniteExterior.coefficientPairing c) (contract_cartan_q i u)
  simp only [map_add, map_neg] at h
  rw [pairing_generator_mul, rootCurrentAction_adjoint]
  exact h

theorem pairing_neutral_q (i : ℕ) (c u : Cochain) :
    FiniteExterior.coefficientPairing (generator (.neutral i) * c) (q u) +
      FiniteExterior.coefficientPairing c (q (contract (.neutral i) u)) = 0 := by
  have h := congrArg (FiniteExterior.coefficientPairing c) (contract_neutral_q i u)
  simp only [map_add, map_zero] at h
  rw [pairing_generator_mul]
  exact h

end KhanSL2.Injectivity.Cartan
