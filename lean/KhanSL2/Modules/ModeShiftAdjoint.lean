module

public import KhanSL2.Modules.ModeShifts

@[expose] public section

/-! The coefficient-raising operator on chains is adjoint to mode lowering on cochains. -/

noncomputable section
set_option maxHeartbeats 1000000
namespace KhanSL2.Modules

def modeContract (v : Mode) : Module.End ℂ Cochain := FiniteExterior.contraction Mode.code v

@[simp] theorem modeContract_one (v : Mode) : modeContract v 1 = 0 := by
  change FiniteExterior.contraction Mode.code v (FiniteExterior.monomial ∅) = 0
  simp

@[simp] theorem modeContract_generator (v w : Mode) :
    modeContract v (generator w) = if v = w then 1 else 0 := by
  change FiniteExterior.contraction Mode.code v (FiniteExterior.monomial {w}) = _
  rw [FiniteExterior.contraction_monomial]
  by_cases h : v = w
  · subst w
    simp [FiniteExterior.position, Finset.filter_singleton]
    rfl
  · simp [h]

theorem modeContract_mul (v : Mode) (u w : Cochain) :
    modeContract v (u * w) = modeContract v u * w + cochainParity u * modeContract v w :=
  FiniteExterior.contraction_wedge Mode.code Mode.code_injective v u w

theorem modeContract_generator_mul (v w : Mode) (u : Cochain) :
    modeContract v (generator w * u) = (if v = w then u else 0) -
      generator w * modeContract v u :=
  FiniteExterior.contraction_generator_wedge Mode.code Mode.code_injective v w u

/-- The contraction transposed from a shifted coefficient generator. -/
def shiftedContract (k : ℕ) : Mode → Module.End ℂ Cochain
  | .b j a => modeContract (.b (j + k) a)
  | .c _ _ => 0

@[simp] theorem shiftedContract_one (k : ℕ) (v : Mode) : shiftedContract k v 1 = 0 := by
  cases v <;> simp [shiftedContract]

theorem shiftedContract_generator_mul (k : ℕ) (v w : Mode) (u : Cochain) :
    shiftedContract k v (generator w * u) =
      shiftedContract k v (generator w) * u - generator w * shiftedContract k v u := by
  cases v <;> simp only [shiftedContract, LinearMap.zero_apply, modeContract_mul,
    cochainParity_generator, neg_mul, zero_mul, mul_zero, sub_zero]; module

theorem modeContract_lowerBGenerator (k : ℕ) (v w : Mode) :
    modeContract v (lowerBGenerator k w) = shiftedContract k v (generator w) := by
  cases v <;> cases w <;>
    simp only [lowerBGenerator, shiftedContract, LinearMap.zero_apply, modeContract_generator,
      map_zero, reduceCtorEq, ite_false]
  all_goals try { split <;> simp_all }
  all_goals split <;> split <;> simp_all <;> omega

theorem modeContract_lowerB (k : ℕ) (v : Mode) (u : Cochain) :
    modeContract v (lowerB k u) = lowerB k (modeContract v u) + shiftedContract k v u := by
  induction u using cochain_induction with
  | hzero => simp
  | hone =>
    change modeContract v (lowerB k 1) = lowerB k (modeContract v 1) + shiftedContract k v 1
    simp
  | hadd u w hu hw => simp only [map_add, hu, hw]; module
  | hsmul a u hu => simp only [map_smul, hu, smul_add]
  | hgen w u hu =>
    change modeContract v (lowerB k (generator w * u)) =
      lowerB k (modeContract v (generator w * u)) + shiftedContract k v (generator w * u)
    rw [lowerB_mul, lowerB_generator, map_add, modeContract_mul, lowerBGenerator_parity,
      modeContract_lowerBGenerator, modeContract_generator_mul, modeContract_generator_mul, map_sub, lowerB_mul,
      lowerB_generator, shiftedContract_generator_mul, hu]
    split <;> simp only [map_zero, neg_mul, mul_add, mul_sub] <;> module

theorem pairing_raiseBGenerator (k : ℕ) (v : Mode) (u w : Cochain) :
    pairing (raiseBGenerator k v * u) w = pairing u (shiftedContract k v w) := by
  cases v with
  | b j a =>
    change FiniteExterior.coefficientPairing (FiniteExterior.generator (Mode.b (j + k) a) * u) w =
      FiniteExterior.coefficientPairing u (FiniteExterior.contraction Mode.code (Mode.b (j + k) a) w)
    exact FiniteExterior.coefficientPairing_generator_mul (Mode.b (j + k) a) u w
  | c j a => simp [raiseBGenerator, shiftedContract]

theorem pairing_mode_generator_mul (v : Mode) (u w : Cochain) :
    pairing (generator v * u) w = pairing u (modeContract v w) :=
  FiniteExterior.coefficientPairing_generator_mul v u w

/-- Exact adjunction on finite chains, before any cycle or quotient assumptions. -/
theorem raiseB_adjoint (k : ℕ) (u v : Cochain) :
    pairing (raiseB k u) v = pairing u (lowerB k v) := by
  refine cochain_induction (P := fun u => ∀ v,
    pairing (raiseB k u) v = pairing u (lowerB k v)) ?_ ?_ ?_ ?_ ?_ u v
  · intro v; simp
  · intro v
    rw [show cochainOne = (1 : Cochain) from rfl, raiseB_one, map_zero, LinearMap.zero_apply]
    change 0 = pairing 1 (FiniteExterior.extendDerivation Mode.code (lowerBGenerator k) v)
    rw [← FiniteExterior.finiteDerivation_eq Mode.code (lowerBGenerator k)
      (FiniteExterior.supportModes v) v (Finset.Subset.refl _),
      FiniteExterior.finiteDerivation_apply, map_sum]
    symm
    apply Finset.sum_eq_zero
    intro a _
    change pairing 1 (lowerBGenerator k a * _) = 0
    cases a with
    | b j a =>
      by_cases h : k ≤ j
      · change pairing 1 ((if k ≤ j then generator (.b (j-k) a) else 0) * _) = 0
        rw [if_pos h]
        exact FiniteExterior.coefficientPairing_one_generator_mul _ _
      · simp [lowerBGenerator, h]
    | c j a => simp [lowerBGenerator]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply, hu, hw]
  · intro a u hu v
    simp only [map_smul, LinearMap.smul_apply, hu]
  · intro a u hu v
    change pairing (raiseB k (generator a * u)) v = pairing (generator a * u) (lowerB k v)
    rw [raiseB_mul, raiseB_generator, map_add, LinearMap.add_apply, pairing_raiseBGenerator,
      pairing_mode_generator_mul, pairing_mode_generator_mul, hu, modeContract_lowerB,
      map_add, add_comm]

/-- The pairing convention used by the cohomology dictionary. -/
theorem pairing_raiseB (k : ℕ) (u : Cochain) (z : Chain) :
    pairing u (raiseB k z) = pairing (lowerB k u) z := by
  rw [FiniteExterior.coefficientPairing_symm, raiseB_adjoint,
    FiniteExterior.coefficientPairing_symm]

end KhanSL2.Modules
