module

public import KhanSL2.Injectivity.ExteriorSubstitution
public import KhanSL2.CELeibniz
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module

/-!
# Explicit Cartan restriction

The Cartan generator is `H = h / 2`, with roots `E = e` and `F = f`.
Their coordinates in the original color basis are `(0,0,i)`, `(i,-1,0)`,
and `(i,1,0)`. Restriction keeps every square-zero-coefficient mode and
only the positive Cartan currents. No quotient of chain invariants is used.
-/

@[expose] public section

noncomputable section
open scoped BigOperators

namespace KhanSL2.Injectivity.Cartan

inductive Mode
  | neutral : ℕ → Mode
  | plus : ℕ → Mode
  | minus : ℕ → Mode
  | cartan : ℕ → Mode
  deriving DecidableEq

def Mode.code : Mode → ℕ
  | .neutral j => 4 * j
  | .plus j => 4 * j + 1
  | .minus j => 4 * j + 2
  | .cartan j => 4 * j + 3

theorem Mode.code_injective : Function.Injective Mode.code := by
  intro a b hab
  cases a <;> cases b <;> simp only [Mode.code] at hab <;> congr <;> omega

instance : FiniteExterior.GeneratorOrder Mode where
  code := Mode.code
  code_injective := Mode.code_injective

abbrev Cochain := FiniteExterior.Exterior Mode

def generator (m : Mode) : Cochain := FiniteExterior.generator m

@[simp] theorem parity_generator (m : Mode) :
    FiniteExterior.parityLinear (generator m) = -generator m :=
  FiniteExterior.parity_generator m

/-- The restriction of each original color coordinate. The Cartan index
is the predecessor index used by the original `Mode.c`. -/
def restrictGenerator : KhanSL2.Mode → Cochain
  | .b j a => ![Complex.I • (generator (.plus j) + generator (.minus j)),
      -generator (.plus j) + generator (.minus j),
      Complex.I • generator (.neutral j)] a
  | .c j a => ![0, 0, Complex.I • generator (.cartan j)] a

theorem restrictGenerator_odd (m : KhanSL2.Mode) :
    FiniteExterior.parityLinear (restrictGenerator m) = -restrictGenerator m := by
  cases m with
  | b j a => fin_cases a <;> simp [restrictGenerator, smul_add, add_comm]
  | c j a => fin_cases a <;> simp [restrictGenerator]

/-- Restriction to positive Cartan currents and all epsilon-colored modes. -/
def restriction : KhanSL2.Cochain →ₐ[ℂ] Cochain :=
  FiniteExterior.substituteOdd restrictGenerator restrictGenerator_odd

@[simp] theorem restriction_generator (m : KhanSL2.Mode) :
    restriction (KhanSL2.generator m) = restrictGenerator m :=
  FiniteExterior.substituteOdd_generator _ _ m

@[simp] theorem restriction_wedge (u v : KhanSL2.Cochain) :
    restriction (wedge u v) = restriction u * restriction v := map_mul restriction u v

/-- The concrete Cartan CE differential on coordinate generators. -/
def qGenerator : Mode → Cochain
  | .neutral _ => 0
  | .cartan _ => 0
  | .plus j => -∑ i ∈ Finset.range j,
      generator (.cartan i) * generator (.plus (j - 1 - i))
  | .minus j => ∑ i ∈ Finset.range j,
      generator (.cartan i) * generator (.minus (j - 1 - i))

def q : Cochain →ₗ[ℂ] Cochain :=
  FiniteExterior.extendDerivation Mode.code qGenerator

@[simp] theorem q_generator (m : Mode) : q (generator m) = qGenerator m := by
  simp [q, generator, FiniteExterior.generator, FiniteExterior.extendDerivation_monomial,
    FiniteExterior.position, Finset.filter_singleton, FiniteExterior.wedge_one_right]

@[simp] theorem q_one : q 1 = 0 := by
  change q (FiniteExterior.monomial ∅) = 0
  simp [q, FiniteExterior.extendDerivation_monomial]

theorem qGenerator_even (m : Mode) :
    FiniteExterior.parityLinear (qGenerator m) = qGenerator m := by
  have hmul (u v : Cochain) : FiniteExterior.parityLinear (u * v) =
      FiniteExterior.parityLinear u * FiniteExterior.parityLinear v :=
    FiniteExterior.parity_wedge Mode.code u v
  cases m <;> simp [qGenerator, hmul]

theorem parity_mul (u v : Cochain) :
    FiniteExterior.parityLinear (u * v) =
      FiniteExterior.parityLinear u * FiniteExterior.parityLinear v :=
  FiniteExterior.parity_wedge Mode.code u v

theorem restriction_parity (u : KhanSL2.Cochain) :
    restriction (cochainParity u) = FiniteExterior.parityLinear (restriction u) := by
  induction u using cochain_induction with
  | hzero => simp
  | hone =>
    change restriction (cochainParity 1) = FiniteExterior.parityLinear (restriction 1)
    rw [map_one, map_one]
    exact FiniteExterior.parity_one.symm
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu =>
    change restriction (cochainParity (KhanSL2.generator m * u)) =
      FiniteExterior.parityLinear (restriction (KhanSL2.generator m * u))
    simp only [map_mul, cochainParity_generator, map_neg, restriction_generator,
      parity_mul, restrictGenerator_odd, hu, neg_mul]

theorem q_mul (u v : Cochain) :
    q (u * v) = q u * v + FiniteExterior.parityLinear u * q v := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_even Mode.code Mode.code_injective
    (qGenerator m) (qGenerator_even m) (FiniteExterior.parityLinear u)).symm

theorem restriction_q_generator (m : KhanSL2.Mode) :
    restriction (KhanSL2.q (KhanSL2.generator m)) = q (restrictGenerator m) := by
  rw [KhanSL2.q_generator]
  cases m with
  | b j a =>
    fin_cases a <;>
      simp [KhanSL2.qGenerator, restrictGenerator, epsilon, Fin.sum_univ_three,
        qGenerator, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I,
        Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib,
        mul_add, mul_neg, smul_add, add_comm]
  | c j a =>
    fin_cases a <;>
      simp [KhanSL2.qGenerator, restrictGenerator, epsilon, Fin.sum_univ_three, qGenerator]

theorem restriction_q (u : KhanSL2.Cochain) :
    restriction (KhanSL2.q u) = q (restriction u) := by
  induction u using cochain_induction with
  | hzero => simp
  | hone =>
    rw [KhanSL2.q_one, map_zero]
    change 0 = q (restriction 1)
    rw [map_one, q_one]
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu =>
    change restriction (KhanSL2.q (KhanSL2.generator m * u)) =
      q (restriction (KhanSL2.generator m * u))
    rw [KhanSL2.q_mul, map_add, map_mul, map_mul, map_mul, q_mul,
      restriction_q_generator, restriction_parity, restriction_generator, hu]

def translationGenerator : Mode → Cochain
  | .neutral j => ((j + 1 : ℕ) : ℂ) • generator (.neutral (j + 1))
  | .plus j => ((j + 1 : ℕ) : ℂ) • generator (.plus (j + 1))
  | .minus j => ((j + 1 : ℕ) : ℂ) • generator (.minus (j + 1))
  | .cartan j => ((j + 2 : ℕ) : ℂ) • generator (.cartan (j + 1))

def translation : Cochain →ₗ[ℂ] Cochain :=
  FiniteExterior.extendDerivation Mode.code translationGenerator

@[simp] theorem translation_generator (m : Mode) :
    translation (generator m) = translationGenerator m := by
  simp [translation, generator, FiniteExterior.generator,
    FiniteExterior.extendDerivation_monomial, FiniteExterior.position, Finset.filter_singleton,
    FiniteExterior.wedge_one_right]

@[simp] theorem translation_one : translation 1 = 0 := by
  change translation (FiniteExterior.monomial ∅) = 0
  simp [translation, FiniteExterior.extendDerivation_monomial]

theorem translationGenerator_odd (m : Mode) :
    FiniteExterior.parityLinear (translationGenerator m) = -translationGenerator m := by
  cases m <;> simp [translationGenerator]

theorem translation_mul (u v : Cochain) :
    translation (u * v) = translation u * v + u * translation v := by
  apply FiniteExterior.extendDerivation_wedge_twist Mode.code Mode.code_injective
  intro m
  exact (FiniteExterior.wedge_comm_of_parity_odd Mode.code Mode.code_injective
    (translationGenerator m) (translationGenerator_odd m) u).symm

theorem restriction_translation_generator (m : KhanSL2.Mode) :
    restriction (KhanSL2.translation (KhanSL2.generator m)) =
      translation (restrictGenerator m) := by
  rw [KhanSL2.translation_generator]
  cases m with
  | b j a =>
    fin_cases a <;>
      simp [KhanSL2.translationGenerator, KhanSL2.Mode.next,
        KhanSL2.Mode.translationCoefficient, restrictGenerator, translationGenerator,
        smul_add, smul_smul, mul_comm]
  | c j a =>
    fin_cases a <;>
      simp [KhanSL2.translationGenerator, KhanSL2.Mode.next,
        KhanSL2.Mode.translationCoefficient, restrictGenerator, translationGenerator,
        smul_smul, mul_comm]

theorem restriction_translation (u : KhanSL2.Cochain) :
    restriction (KhanSL2.translation u) = translation (restriction u) := by
  induction u using cochain_induction with
  | hzero => simp
  | hone =>
    change restriction (KhanSL2.translation 1) = translation (restriction 1)
    rw [map_one restriction, translation_one]
    change restriction (KhanSL2.extendDerivation KhanSL2.translationGenerator cochainOne) = 0
    rw [KhanSL2.extendDerivation_one, map_zero]
  | hadd u v hu hv => simp only [map_add, hu, hv]
  | hsmul r u hu => simp only [map_smul, hu]
  | hgen m u hu =>
    change restriction (KhanSL2.translation (KhanSL2.generator m * u)) =
      translation (restriction (KhanSL2.generator m * u))
    rw [KhanSL2.translation_mul, map_add, map_mul, map_mul, map_mul, translation_mul,
      restriction_translation_generator, restriction_generator, hu]

theorem restriction_translation_pow (n : ℕ) (u : KhanSL2.Cochain) :
    restriction ((KhanSL2.translation ^ n) u) = (translation ^ n) (restriction u) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply,
      restriction_translation, hn]

theorem restriction_xRepresentative :
    restriction xRepresentative = generator (.neutral 0) * generator (.cartan 0) := by
  change restriction (-∑ a : Fin 3,
    KhanSL2.generator (.b 0 a) * KhanSL2.generator (.c 0 a)) = _
  simp [Fin.sum_univ_three, restrictGenerator, smul_mul_assoc, mul_smul_comm,
    smul_smul, Complex.I_mul_I]

@[simp] theorem generator_sq_zero (m : Mode) : generator m * generator m = 0 :=
  FiniteExterior.odd_sq_zero _ (parity_generator m)

theorem generator_anticommute (m n : Mode) :
    generator m * generator n = -(generator n * generator m) :=
  FiniteExterior.odd_mul_odd _ _ (parity_generator m) (parity_generator n)

theorem restriction_yRepresentative :
    restriction yRepresentative =
      (-2 : ℂ) • ((generator (.neutral 0) * generator (.plus 0)) * generator (.minus 0)) := by
  change restriction ((KhanSL2.generator (.b 0 0) * KhanSL2.generator (.b 0 1)) *
    KhanSL2.generator (.b 0 2)) = _
  rw [map_mul, map_mul, restriction_generator, restriction_generator,
    restriction_generator]
  change ((Complex.I • (generator (.plus 0) + generator (.minus 0))) *
    (-generator (.plus 0) + generator (.minus 0))) *
    (Complex.I • generator (.neutral 0)) = _
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, Complex.I_mul_I]
  have hnp : generator (.minus 0) * generator (.plus 0) =
      -(generator (.plus 0) * generator (.minus 0)) := generator_anticommute _ _
  have hrotate : (generator (.plus 0) * generator (.minus 0)) * generator (.neutral 0) =
      (generator (.neutral 0) * generator (.plus 0)) * generator (.minus 0) := by
    rw [mul_assoc, generator_anticommute (.minus 0) (.neutral 0), mul_neg,
      ← mul_assoc, generator_anticommute (.plus 0) (.neutral 0), neg_mul, neg_neg]
  simp only [add_mul, mul_add, neg_mul, mul_neg, generator_sq_zero,
    neg_zero, hnp, neg_neg, zero_add, add_zero, hrotate]
  module

end KhanSL2.Injectivity.Cartan
