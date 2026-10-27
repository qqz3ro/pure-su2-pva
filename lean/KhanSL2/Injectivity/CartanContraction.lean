module

public import KhanSL2.Injectivity.CartanRestriction
public import KhanSL2.Injectivity.FinitePairing

/-! Cartan contraction and the downward current action on finite cochains. -/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace KhanSL2.Injectivity.Cartan

def contract (m : Mode) : Cochain →ₗ[ℂ] Cochain :=
  FiniteExterior.contraction Mode.code m

@[simp] theorem contract_one (m : Mode) : contract m 1 = 0 := by
  change FiniteExterior.contraction Mode.code m (FiniteExterior.monomial ∅) = 0
  simp

@[simp] theorem contract_generator (m n : Mode) :
    contract m (generator n) = if m = n then 1 else 0 := by
  change FiniteExterior.contraction Mode.code m (FiniteExterior.monomial {n}) = _
  rw [FiniteExterior.contraction_monomial]
  by_cases h : m = n
  · subst n
    simp [FiniteExterior.position, Finset.filter_singleton]
    rfl
  · simp [h]

theorem contract_mul (m : Mode) (u v : Cochain) :
    contract m (u * v) = contract m u * v +
      FiniteExterior.parityLinear u * contract m v :=
  FiniteExterior.contraction_wedge Mode.code Mode.code_injective m u v

theorem contract_generator_mul (m n : Mode) (u : Cochain) :
    contract m (generator n * u) = (if m = n then u else 0) -
      generator n * contract m u := by
  exact FiniteExterior.contraction_generator_wedge Mode.code Mode.code_injective m n u

def loweringGenerator (k : ℕ) : Mode → Cochain
  | .plus j => if k ≤ j then generator (.plus (j - k)) else 0
  | .minus j => if k ≤ j then -generator (.minus (j - k)) else 0
  | .neutral _ => 0
  | .cartan _ => 0

def lowering (k : ℕ) : Cochain →ₗ[ℂ] Cochain :=
  FiniteExterior.extendDerivation Mode.code (loweringGenerator k)

@[simp] theorem lowering_generator (k : ℕ) (m : Mode) :
    lowering k (generator m) = loweringGenerator k m := by
  simp [lowering, generator, FiniteExterior.generator,
    FiniteExterior.extendDerivation_monomial, FiniteExterior.position,
    Finset.filter_singleton, FiniteExterior.wedge_one_right]

@[simp] theorem lowering_one (k : ℕ) : lowering k 1 = 0 := by
  change lowering k (FiniteExterior.monomial ∅) = 0
  simp [lowering, FiniteExterior.extendDerivation_monomial]

theorem loweringGenerator_odd (k : ℕ) (m : Mode) :
    FiniteExterior.parityLinear (loweringGenerator k m) = -loweringGenerator k m := by
  cases m <;> simp [loweringGenerator] <;> split <;> simp

theorem lowering_mul (k : ℕ) (u v : Cochain) :
    lowering k (u * v) = lowering k u * v + u * lowering k v := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_odd Mode.code Mode.code_injective
    (loweringGenerator k m) (loweringGenerator_odd k m) u).symm

theorem contract_cartan_qGenerator (i : ℕ) (m : Mode) :
    contract (.cartan i) (qGenerator m) = -loweringGenerator (i + 1) m := by
  cases m with
  | neutral j => simp [qGenerator, loweringGenerator]
  | cartan j => simp [qGenerator, loweringGenerator]
  | plus j =>
    simp only [qGenerator, map_neg, map_sum, contract_generator_mul,
      contract_generator, Mode.cartan.injEq, reduceCtorEq, ite_false, mul_zero, sub_zero]
    by_cases h : i < j
    · have hk : i + 1 ≤ j := by omega
      have he : j - 1 - i = j - (i + 1) := by omega
      simp [Finset.mem_range, h, loweringGenerator, hk, he]
    · have hk : ¬i + 1 ≤ j := by omega
      simp [Finset.mem_range, h, loweringGenerator, hk]
  | minus j =>
    simp only [qGenerator, map_sum, contract_generator_mul,
      contract_generator, Mode.cartan.injEq, reduceCtorEq, ite_false, mul_zero, sub_zero]
    by_cases h : i < j
    · have hk : i + 1 ≤ j := by omega
      have he : j - 1 - i = j - (i + 1) := by omega
      simp [Finset.mem_range, h, loweringGenerator, hk, he]
    · have hk : ¬i + 1 ≤ j := by omega
      simp [Finset.mem_range, h, loweringGenerator, hk]

theorem contract_neutral_qGenerator (i : ℕ) (m : Mode) :
    contract (.neutral i) (qGenerator m) = 0 := by
  cases m <;> simp [qGenerator, contract_generator_mul]

/-- Cartan contraction of the CE differential is minus the downward current action. -/
theorem contract_cartan_q (i : ℕ) (u : Cochain) :
    contract (.cartan i) (q u) + q (contract (.cartan i) u) =
      -lowering (i + 1) u := by
  refine FiniteExterior.induction_on Mode.code (P := fun u =>
    contract (.cartan i) (q u) + q (contract (.cartan i) u) =
      -lowering (i + 1) u) ?_ ?_ ?_ ?_ ?_ u
  · simp
  · change contract (.cartan i) (q 1) + q (contract (.cartan i) 1) = -lowering (i + 1) 1
    simp
  · intro u v hu hv
    simp only [map_add]
    rw [add_add_add_comm, hu, hv, neg_add]
  · intro r u hu
    simp only [map_smul]
    rw [← smul_add, hu, smul_neg]
  · intro m u hu
    change contract (.cartan i) (q (generator m * u)) +
      q (contract (.cartan i) (generator m * u)) = -lowering (i + 1) (generator m * u)
    have hmul := congrArg (fun w => generator m * w) hu
    simp only [mul_add, mul_neg] at hmul
    rw [q_mul, q_generator, parity_generator, neg_mul, ← sub_eq_add_neg, map_sub,
      contract_mul, qGenerator_even, contract_cartan_qGenerator,
      contract_generator_mul, contract_generator_mul, map_sub, q_mul,
      q_generator, parity_generator, lowering_mul, lowering_generator]
    split <;> simp only [map_zero, neg_mul, mul_add, mul_neg] at *
    all_goals
      calc
        _ = -(loweringGenerator (i + 1) m * u) +
            (generator m * contract (.cartan i) (q u) +
              generator m * q (contract (.cartan i) u)) := by module
        _ = _ := by rw [hmul]; module

theorem contract_neutral_q (i : ℕ) (u : Cochain) :
    contract (.neutral i) (q u) + q (contract (.neutral i) u) = 0 := by
  refine FiniteExterior.induction_on Mode.code (P := fun u =>
    contract (.neutral i) (q u) + q (contract (.neutral i) u) = 0)
      ?_ ?_ ?_ ?_ ?_ u
  · simp
  · change contract (.neutral i) (q 1) + q (contract (.neutral i) 1) = 0
    simp
  · intro u v hu hv
    simp only [map_add]
    rw [add_add_add_comm, hu, hv, zero_add]
  · intro r u hu
    simp only [map_smul]
    rw [← smul_add, hu, smul_zero]
  · intro m u hu
    change contract (.neutral i) (q (generator m * u)) +
      q (contract (.neutral i) (generator m * u)) = _
    have hmul := congrArg (fun w => generator m * w) hu
    simp only [mul_add, mul_zero] at hmul
    rw [q_mul, q_generator, parity_generator, neg_mul, ← sub_eq_add_neg, map_sub,
      contract_mul, qGenerator_even, contract_neutral_qGenerator,
      contract_generator_mul, contract_generator_mul, map_sub, q_mul,
      q_generator, parity_generator]
    split <;> simp only [map_zero, neg_mul, zero_mul, zero_add] at *
    all_goals
      calc
        _ = generator m * contract (.neutral i) (q u) +
            generator m * q (contract (.neutral i) u) := by module
        _ = 0 := hmul

end KhanSL2.Injectivity.Cartan
