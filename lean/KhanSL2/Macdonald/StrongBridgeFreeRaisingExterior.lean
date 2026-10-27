module

public import KhanSL2.Macdonald.ShiftAdjoint
public import KhanSL2.Modules.ModeShiftAdjoint

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Explicit shifts on every positive exterior coordinate and their transpose.
The operators are specified on generators, independently of any homology map. -/
noncomputable section
open scoped BigOperators
namespace KhanSL2.Macdonald

/-- Raise the index of an odd free generator by m. -/
def freeOddRaiseGenerator (m : ℕ) (v : Mode) : Exterior :=
  FiniteExterior.generator (⟨v.index + m, v.color⟩ : Mode)

/-- Lower an odd free generator, vanishing at the lower boundary. -/
def freeOddLowerGenerator (m : ℕ) (v : Mode) : Exterior :=
  if m ≤ v.index then FiniteExterior.generator (⟨v.index-m, v.color⟩ : Mode) else 0

def freeOddRaise (m : ℕ) : Module.End ℂ Exterior :=
  FiniteExterior.extendDerivation BGG.PositiveCE.Mode.code (freeOddRaiseGenerator m)

def freeOddLower (m : ℕ) : Module.End ℂ Exterior :=
  FiniteExterior.extendDerivation BGG.PositiveCE.Mode.code (freeOddLowerGenerator m)

@[simp] theorem freeOddRaise_generator (m : ℕ) (v : Mode) :
    freeOddRaise m (FiniteExterior.generator v) = freeOddRaiseGenerator m v :=
by
  change FiniteExterior.extendDerivation BGG.PositiveCE.Mode.code _
    (FiniteExterior.monomial {v}) = _
  rw [FiniteExterior.extendDerivation_monomial]
  simp only [Finset.sum_singleton, Finset.erase_singleton]
  have hp : FiniteExterior.position BGG.PositiveCE.Mode.code v {v} = 0 := by
    simp [FiniteExterior.position, Finset.filter_singleton]
  rw [hp, pow_zero, one_smul]
  exact mul_one _

@[simp] theorem freeOddLower_generator (m : ℕ) (v : Mode) :
    freeOddLower m (FiniteExterior.generator v) = freeOddLowerGenerator m v :=
by
  change FiniteExterior.extendDerivation BGG.PositiveCE.Mode.code _
    (FiniteExterior.monomial {v}) = _
  rw [FiniteExterior.extendDerivation_monomial]
  simp only [Finset.sum_singleton, Finset.erase_singleton]
  have hp : FiniteExterior.position BGG.PositiveCE.Mode.code v {v} = 0 := by
    simp [FiniteExterior.position, Finset.filter_singleton]
  rw [hp, pow_zero, one_smul]
  exact mul_one _

@[simp] theorem freeOddRaise_one (m : ℕ) : freeOddRaise m 1 = 0 :=
by
  change FiniteExterior.extendDerivation BGG.PositiveCE.Mode.code _
    (FiniteExterior.monomial ∅) = 0
  simp

@[simp] theorem freeOddLower_one (m : ℕ) : freeOddLower m 1 = 0 :=
by
  change FiniteExterior.extendDerivation BGG.PositiveCE.Mode.code _
    (FiniteExterior.monomial ∅) = 0
  simp

theorem freeOddRaiseGenerator_parity (m : ℕ) (v : Mode) :
    FiniteExterior.parityLinear (freeOddRaiseGenerator m v) = -freeOddRaiseGenerator m v :=
  FiniteExterior.parity_generator _

theorem freeOddLowerGenerator_parity (m : ℕ) (v : Mode) :
    FiniteExterior.parityLinear (freeOddLowerGenerator m v) = -freeOddLowerGenerator m v := by
  unfold freeOddLowerGenerator
  split <;> simp

theorem freeOddRaise_mul (m : ℕ) (u v : Exterior) :
    freeOddRaise m (u * v) = freeOddRaise m u * v + u * freeOddRaise m v := by
  apply FiniteExterior.extendDerivation_wedge_twist
    BGG.PositiveCE.Mode.code BGG.PositiveCE.Mode.code_injective
  intro a
  exact (FiniteExterior.wedge_comm_of_parity_odd
    BGG.PositiveCE.Mode.code BGG.PositiveCE.Mode.code_injective
    (freeOddRaiseGenerator m a) (freeOddRaiseGenerator_parity m a) u).symm

theorem freeOddLower_mul (m : ℕ) (u v : Exterior) :
    freeOddLower m (u * v) = freeOddLower m u * v + u * freeOddLower m v := by
  apply FiniteExterior.extendDerivation_wedge_twist
    BGG.PositiveCE.Mode.code BGG.PositiveCE.Mode.code_injective
  intro a
  exact (FiniteExterior.wedge_comm_of_parity_odd
    BGG.PositiveCE.Mode.code BGG.PositiveCE.Mode.code_injective
    (freeOddLowerGenerator m a) (freeOddLowerGenerator_parity m a) u).symm

def freeOddContract (v : Mode) : Module.End ℂ Exterior :=
  FiniteExterior.contraction BGG.PositiveCE.Mode.code v

@[simp] theorem freeOddContract_one (v : Mode) : freeOddContract v 1 = 0 := by
  change FiniteExterior.contraction BGG.PositiveCE.Mode.code v (FiniteExterior.monomial ∅) = 0
  simp

@[simp] theorem freeOddContract_generator (v w : Mode) :
    freeOddContract v (FiniteExterior.generator w) = if v = w then 1 else 0 := by
  change FiniteExterior.contraction BGG.PositiveCE.Mode.code v (FiniteExterior.monomial {w}) = _
  rw [FiniteExterior.contraction_monomial]
  by_cases h : v = w
  · subst w
    simp [FiniteExterior.position, Finset.filter_singleton]
    rfl
  · simp [h]

theorem freeOddContract_mul (v : Mode) (u w : Exterior) :
    freeOddContract v (u * w) = freeOddContract v u * w +
      FiniteExterior.parityLinear u * freeOddContract v w :=
  FiniteExterior.contraction_wedge BGG.PositiveCE.Mode.code BGG.PositiveCE.Mode.code_injective v u w

theorem freeOddContract_generator_mul (v w : Mode) (u : Exterior) :
    freeOddContract v (FiniteExterior.generator w * u) = (if v = w then u else 0) -
      FiniteExterior.generator w * freeOddContract v u :=
  FiniteExterior.contraction_generator_wedge
    BGG.PositiveCE.Mode.code BGG.PositiveCE.Mode.code_injective v w u

/-- The contraction at the raised index, dual to raising one generator. -/
def freeOddShiftedContract (m : ℕ) (v : Mode) : Module.End ℂ Exterior :=
  freeOddContract ⟨v.index+m,v.color⟩

@[simp] theorem freeOddShiftedContract_one (m : ℕ) (v : Mode) :
    freeOddShiftedContract m v 1 = 0 := freeOddContract_one _

theorem freeOddShiftedContract_generator_mul (m : ℕ) (v w : Mode) (u : Exterior) :
    freeOddShiftedContract m v (FiniteExterior.generator w * u) =
      freeOddShiftedContract m v (FiniteExterior.generator w) * u -
        FiniteExterior.generator w * freeOddShiftedContract m v u := by
  simp only [freeOddShiftedContract, freeOddContract_mul,
    FiniteExterior.parity_generator, neg_mul]
  module

theorem freeOddContract_lowerGenerator (m : ℕ) (v w : Mode) :
    freeOddContract v (freeOddLowerGenerator m w) =
      freeOddShiftedContract m v (FiniteExterior.generator w) := by
  have he (h : m ≤ w.index) :
      v = (⟨w.index-m,w.color⟩ : Mode) ↔ (⟨v.index+m,v.color⟩ : Mode) = w := by
    constructor
    · intro hv
      apply BGG.PositiveCE.Mode.ext
      · have hi := congrArg BGG.PositiveCE.Mode.index hv
        change v.index + m = w.index
        change v.index = w.index-m at hi
        omega
      · simpa only [] using congrArg BGG.PositiveCE.Mode.color hv
    · intro hv
      apply BGG.PositiveCE.Mode.ext
      · have hi := congrArg BGG.PositiveCE.Mode.index hv
        change v.index = w.index-m
        change v.index+m = w.index at hi
        omega
      · simpa only [] using congrArg BGG.PositiveCE.Mode.color hv
  by_cases h : m ≤ w.index
  · simp only [freeOddLowerGenerator, if_pos h, freeOddShiftedContract,
      freeOddContract_generator, he h]
  · have hn : (⟨v.index+m,v.color⟩ : Mode) ≠ w := by
      intro hv
      have hi := congrArg BGG.PositiveCE.Mode.index hv
      change v.index+m = w.index at hi
      omega
    simp [freeOddLowerGenerator, h, freeOddShiftedContract, hn]

theorem freeOddContract_lower (m : ℕ) (v : Mode) (u : Exterior) :
    freeOddContract v (freeOddLower m u) =
      freeOddLower m (freeOddContract v u) + freeOddShiftedContract m v u := by
  refine FiniteExterior.induction_on BGG.PositiveCE.Mode.code
    (P := fun u => freeOddContract v (freeOddLower m u) =
      freeOddLower m (freeOddContract v u) + freeOddShiftedContract m v u) ?_ ?_ ?_ ?_ ?_ u
  · simp
  · change freeOddContract v (freeOddLower m 1) =
      freeOddLower m (freeOddContract v 1) + freeOddShiftedContract m v 1
    simp
  · intro u w hu hw
    simp only [map_add, hu, hw]
    module
  · intro a u hu
    simp only [map_smul, hu, smul_add]
  · intro w u hu
    change freeOddContract v (freeOddLower m (FiniteExterior.generator w * u)) =
      freeOddLower m (freeOddContract v (FiniteExterior.generator w * u)) +
        freeOddShiftedContract m v (FiniteExterior.generator w * u)
    rw [freeOddLower_mul, freeOddLower_generator, map_add, freeOddContract_mul,
      freeOddLowerGenerator_parity, freeOddContract_lowerGenerator,
      freeOddContract_generator_mul, freeOddContract_generator_mul, map_sub,
      freeOddLower_mul, freeOddLower_generator, freeOddShiftedContract_generator_mul, hu]
    split <;> simp only [map_zero, neg_mul, mul_add, mul_sub] <;> module

theorem pairing_freeOddRaiseGenerator (m : ℕ) (v : Mode) (u w : Exterior) :
    FiniteExterior.coefficientPairing (freeOddRaiseGenerator m v * u) w =
      FiniteExterior.coefficientPairing u (freeOddShiftedContract m v w) :=
  FiniteExterior.coefficientPairing_generator_mul _ u w

theorem pairing_freeOddGenerator_mul (v : Mode) (u w : Exterior) :
    FiniteExterior.coefficientPairing (FiniteExterior.generator v * u) w =
      FiniteExterior.coefficientPairing u (freeOddContract v w) :=
  FiniteExterior.coefficientPairing_generator_mul v u w

/-- Raising and lowering are transposes for the actual finite exterior pairing. -/
theorem freeOddRaise_adjoint (m : ℕ) (u v : Exterior) :
    FiniteExterior.coefficientPairing (freeOddRaise m u) v =
      FiniteExterior.coefficientPairing u (freeOddLower m v) := by
  refine FiniteExterior.induction_on BGG.PositiveCE.Mode.code
    (P := fun u => ∀ v, FiniteExterior.coefficientPairing (freeOddRaise m u) v =
      FiniteExterior.coefficientPairing u (freeOddLower m v)) ?_ ?_ ?_ ?_ ?_ u v
  · intro v
    simp
  · intro v
    change FiniteExterior.coefficientPairing (freeOddRaise m 1) v =
      FiniteExterior.coefficientPairing 1 (freeOddLower m v)
    rw [freeOddRaise_one, map_zero, LinearMap.zero_apply]
    change 0 = FiniteExterior.coefficientPairing 1
      (FiniteExterior.extendDerivation BGG.PositiveCE.Mode.code (freeOddLowerGenerator m) v)
    rw [← FiniteExterior.finiteDerivation_eq BGG.PositiveCE.Mode.code (freeOddLowerGenerator m)
      (FiniteExterior.supportModes v) v (Finset.Subset.refl _),
      FiniteExterior.finiteDerivation_apply, map_sum]
    symm
    apply Finset.sum_eq_zero
    intro a _
    change FiniteExterior.coefficientPairing 1 (freeOddLowerGenerator m a * _) = 0
    by_cases h : m ≤ a.index
    · rw [freeOddLowerGenerator, if_pos h]
      exact FiniteExterior.coefficientPairing_one_generator_mul _ _
    · simp [freeOddLowerGenerator, h]
  · intro u w hu hw v
    simp only [map_add, LinearMap.add_apply, hu, hw]
  · intro a u hu v
    simp only [map_smul, LinearMap.smul_apply, hu]
  · intro a u hu v
    change FiniteExterior.coefficientPairing (freeOddRaise m (FiniteExterior.generator a * u)) v =
      FiniteExterior.coefficientPairing (FiniteExterior.generator a * u) (freeOddLower m v)
    rw [freeOddRaise_mul, freeOddRaise_generator, map_add, LinearMap.add_apply,
      pairing_freeOddRaiseGenerator, pairing_freeOddGenerator_mul,
      pairing_freeOddGenerator_mul, hu, freeOddContract_lower, map_add, add_comm]

end KhanSL2.Macdonald
