module

public import KhanSL2.SourceBracketQuotient
public import KhanSL2.SourceJacobiExtension

@[expose] public section

/-! # All eight generator Jacobi identities for the actual source bracket -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.Source

open LambdaPolynomial LambdaBracket SourceGeneratorChecks

def generatorJet : Kind → ℕ → Source
  | .X, n => X n
  | .Y, n => Y n

def generator (a : Kind) : Source := generatorJet a 0

theorem generator_mem (a : Kind) : generator a ∈ piece (SourceGeneratorChecks.generatorDegree a) := by
  cases a with
  | X => exact X_mem 0
  | Y => exact Y_mem 0

@[simp] theorem generatorJet_translation (a : Kind) (i : ℕ) :
    translation (generatorJet a i) = generatorJet a (i + 1) := by
  cases a <;> rfl

@[simp] theorem generator_bracket_zero_zero (a b : Kind) :
    bracket (generatorJet a 0) (generatorJet b 0) =
      Finsupp.single 0 (derivativeCoefficient a b • generatorJet (outputKind a b) 1) +
      Finsupp.single 1 (variableCoefficient a b • generatorJet (outputKind a b) 0) := by
  cases a <;> cases b <;>
    simp [generatorJet, derivativeCoefficient, variableCoefficient, outputKind,
      XX, XY, YX, jetAction]

@[simp] theorem generator_bracket_one_zero (a b : Kind) :
    bracket (generatorJet a 1) (generatorJet b 0) =
      -(Finsupp.single 1 (derivativeCoefficient a b • generatorJet (outputKind a b) 1) +
        Finsupp.single 2 (variableCoefficient a b • generatorJet (outputKind a b) 0)) := by
  rw [← generatorJet_translation a 0, bracket_left_translation,
    generator_bracket_zero_zero, shift_add, shift_single, shift_single]

@[simp] theorem generator_bracket_zero_one (a b : Kind) :
    bracket (generatorJet a 0) (generatorJet b 1) =
      (Finsupp.single 0 (derivativeCoefficient a b • generatorJet (outputKind a b) 2) +
        Finsupp.single 1 (variableCoefficient a b • generatorJet (outputKind a b) 1)) +
      (Finsupp.single 1 (derivativeCoefficient a b • generatorJet (outputKind a b) 1) +
        Finsupp.single 2 (variableCoefficient a b • generatorJet (outputKind a b) 0)) := by
  rw [← generatorJet_translation b 0, bracket_right_translation,
    generator_bracket_zero_zero, rightTranslation_apply]
  simp

private def middleOnPolynomial (c : Source) :
    LambdaPolynomial Source →ₗ[ℂ] TwoLambdaPolynomial Source :=
  Finsupp.lsum ℂ fun r => (expand r).comp (bracket.flip c)

private theorem middleOnPolynomial_apply (a b c : Source) :
    middleOnPolynomial c (bracket a b) = bracket.jacobiMiddle a b c := by
  change (bracket a b).sum (fun r v => expand r (bracket v c)) = _
  simp only [expand_apply, LambdaBracket.jacobiMiddle]

@[simp] private theorem middleOnPolynomial_single (c v : Source) (r : ℕ) :
    middleOnPolynomial c (Finsupp.single r v) = expand r (bracket v c) := by
  simp [middleOnPolynomial, Finsupp.lsum_single]

set_option maxHeartbeats 1000000 in
theorem generator_super_jacobi (a b c : Kind) :
    bracket.jacobiLeft (generator a) (generator b) (generator c) =
      bracket.jacobiMiddle (generator a) (generator b) (generator c) +
        koszulSign (SourceGeneratorChecks.generatorDegree a) (SourceGeneratorChecks.generatorDegree b) •
          bracket.jacobiRight (generator a) (generator b) (generator c) := by
  change leftOnPolynomial bracket (generator a) (bracket (generator b) (generator c)) =
    bracket.jacobiMiddle (generator a) (generator b) (generator c) +
      koszulSign (SourceGeneratorChecks.generatorDegree a) (SourceGeneratorChecks.generatorDegree b) •
        rightOnPolynomial bracket (generator b) (bracket (generator a) (generator c))
  rw [← middleOnPolynomial_apply]
  cases a <;> cases b <;> cases c <;>
    simp only [generator, generator_bracket_zero_zero, outputKind,
      derivativeCoefficient, variableCoefficient, SourceGeneratorChecks.generatorDegree, koszulSign]
  all_goals norm_num
  all_goals
    simp [outputKind, derivativeCoefficient, variableCoefficient,
      smul_add, add_smul, smul_smul, Finset.sum_range_succ,
      LinearMap.add_apply, LinearMap.smul_apply]
  all_goals simp only [← Finsupp.smul_single]
  all_goals module

/-- The eight base cases for the full super-Jacobi extension theorem. -/
theorem generator_jacobiator (a b c : Kind) :
    LambdaBracket.jacobiator bracket
      (koszulSign (SourceGeneratorChecks.generatorDegree a) (SourceGeneratorChecks.generatorDegree b))
      (generator a) (generator b) (generator c) = 0 :=
  (LambdaBracket.jacobiator_eq_zero_iff _ _ _ _ _).mpr (generator_super_jacobi a b c)

end KhanSL2.Source
