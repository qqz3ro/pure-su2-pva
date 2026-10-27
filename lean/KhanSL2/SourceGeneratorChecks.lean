module

public import KhanSL2.SourceData
public import KhanSL2.LambdaPolynomialLemmas
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Checks on the proposed source generator bracket

The first part constructs an unconditional bracket on the free module on
`X, ∂X, ...` and `Y, ∂Y, ...`, and checks the generator super-Jacobi equations
using the exact polynomial expressions from `PVA.lean`.

These finite checks do not assert that the bracket has been extended to the
source algebra, or that the full PVA laws hold on that algebra.
-/

noncomputable section

open scoped BigOperators

namespace KhanSL2.SourceGeneratorChecks

theorem differentiated_X0_sq :
    Source.X 1 * Source.X 0 + Source.X 0 * Source.X 1 = 0 := by
  have h := congrArg Source.translation Source.X0_sq
  simpa only [Source.translation_mul, Source.translation_X, map_zero] using h

theorem differentiated_X0_Y0 :
    Source.X 1 * Source.Y 0 + Source.X 0 * Source.Y 1 = 0 := by
  have h := congrArg Source.translation Source.X0_Y0
  simpa only [Source.translation_mul, Source.translation_X, Source.translation_Y,
    map_zero] using h

theorem differentiated_X0_Y1 :
    Source.X 1 * Source.Y 1 + Source.X 0 * Source.Y 2 = 0 := by
  have h := congrArg Source.translation Source.X0_Y1
  simpa only [Source.translation_mul, Source.translation_X, Source.translation_Y,
    map_zero] using h

theorem differentiated_Y0_Y1 :
    Source.Y 1 * Source.Y 1 + Source.Y 0 * Source.Y 2 = 0 := by
  have h := congrArg Source.translation Source.Y0_Y1
  simpa only [Source.translation_mul, Source.translation_Y, map_zero] using h

@[simp]
theorem X1_Y0 : Source.X 1 * Source.Y 0 = 0 := by
  simpa using differentiated_X0_Y0

@[simp]
theorem Y0_Y2 : Source.Y 0 * Source.Y 2 = 0 := by
  simpa using differentiated_Y0_Y1

inductive Kind
  | X
  | Y
  deriving DecidableEq

abbrev Jet := Kind × ℕ
abbrev JetModule := Jet →₀ ℂ

def jet (a : Kind) (n : ℕ) : JetModule := Finsupp.single (a, n) 1

def jetTranslation : Module.End ℂ JetModule :=
  Finsupp.linearCombination ℂ fun a : Jet => jet a.1 (a.2 + 1)

@[simp]
theorem jetTranslation_jet (a : Kind) (n : ℕ) :
    jetTranslation (jet a n) = jet a (n + 1) := by
  simp [jetTranslation, jet, Finsupp.linearCombination_single]

def outputKind : Kind → Kind → Kind
  | .X, .X => .X
  | _, _ => .Y

def derivativeCoefficient : Kind → Kind → ℂ
  | .X, .X => 1
  | .X, .Y => 1
  | .Y, .X => 2
  | .Y, .Y => 0

def variableCoefficient : Kind → Kind → ℂ
  | .X, .X => 2
  | .X, .Y => 3
  | .Y, .X => 3
  | .Y, .Y => 0

/-- The closed sesquilinear extension
`{∂^m a _λ ∂^n b} = (-λ)^m (∂ + λ)^n {a _λ b}`. -/
def bracketOnJets (a b : Jet) : LambdaPolynomial JetModule :=
  ∑ i ∈ Finset.range (b.2 + 1),
    ((-1 : ℂ) ^ a.2 * (Nat.choose b.2 i : ℂ)) •
      (Finsupp.single (a.2 + i)
        (derivativeCoefficient a.1 b.1 • jet (outputKind a.1 b.1) (b.2 - i + 1)) +
       Finsupp.single (a.2 + i + 1)
        (variableCoefficient a.1 b.1 • jet (outputKind a.1 b.1) (b.2 - i)))

/-- A concrete bilinear bracket on the free jet module. -/
def jetBracket : LambdaBracket JetModule :=
  Finsupp.linearCombination ℂ fun a =>
    Finsupp.linearCombination ℂ fun b => bracketOnJets a b

theorem jetBracket_jet (a b : Kind) (m n : ℕ) :
    jetBracket (jet a m) (jet b n) = bracketOnJets (a, m) (b, n) := by
  simp [jetBracket, jet, Finsupp.linearCombination_single]

@[simp]
theorem jetBracket_zero_zero (a b : Kind) :
    jetBracket (jet a 0) (jet b 0) =
      Finsupp.single 0 (derivativeCoefficient a b • jet (outputKind a b) 1) +
      Finsupp.single 1 (variableCoefficient a b • jet (outputKind a b) 0) := by
  simp only [jetBracket_jet, bracketOnJets]
  norm_num [Finset.sum_range_succ]
  all_goals exact one_smul _ _

@[simp]
theorem jetBracket_one_zero (a b : Kind) :
    jetBracket (jet a 1) (jet b 0) =
      -(Finsupp.single 1 (derivativeCoefficient a b • jet (outputKind a b) 1) +
        Finsupp.single 2 (variableCoefficient a b • jet (outputKind a b) 0)) := by
  simp only [jetBracket_jet, bracketOnJets]
  norm_num [Finset.sum_range_succ]
  all_goals module

@[simp]
theorem jetBracket_zero_one (a b : Kind) :
    jetBracket (jet a 0) (jet b 1) =
      (Finsupp.single 0 (derivativeCoefficient a b • jet (outputKind a b) 2) +
        Finsupp.single 1 (variableCoefficient a b • jet (outputKind a b) 1)) +
      (Finsupp.single 1 (derivativeCoefficient a b • jet (outputKind a b) 1) +
        Finsupp.single 2 (variableCoefficient a b • jet (outputKind a b) 0)) := by
  simp only [jetBracket_jet, bracketOnJets]
  norm_num [Finset.sum_range_succ]
  all_goals module

def generatorDegree : Kind → Degree
  | .X => (2, 1, 2)
  | .Y => (3, 3, 3)

theorem jetBracket_XX :
    jetBracket (jet .X 0) (jet .X 0) =
      Finsupp.single 0 (jet .X 1) +
      Finsupp.single 1 ((2 : ℂ) • jet .X 0) := by
  simp [bracketOnJets, outputKind, derivativeCoefficient, variableCoefficient]

theorem jetBracket_XY :
    jetBracket (jet .X 0) (jet .Y 0) =
      Finsupp.single 0 (jet .Y 1) +
      Finsupp.single 1 ((3 : ℂ) • jet .Y 0) := by
  simp [bracketOnJets, outputKind, derivativeCoefficient, variableCoefficient]

theorem jetBracket_YX :
    jetBracket (jet .Y 0) (jet .X 0) =
      Finsupp.single 0 ((2 : ℂ) • jet .Y 1) +
      Finsupp.single 1 ((3 : ℂ) • jet .Y 0) := by
  simp [bracketOnJets, outputKind, derivativeCoefficient, variableCoefficient]

theorem jetBracket_YY :
    jetBracket (jet .Y 0) (jet .Y 0) = 0 := by
  simp [bracketOnJets, outputKind, derivativeCoefficient, variableCoefficient]

theorem generator_super_skew (a b : Kind) :
    jetBracket (jet a 0) (jet b 0) =
      (-koszulSign (generatorDegree a) (generatorDegree b)) •
        (jetBracket (jet b 0) (jet a 0)).minusVariableMinusTranslation jetTranslation := by
  cases a <;> cases b <;>
    simp only [jetBracket_zero_zero, outputKind, derivativeCoefficient, variableCoefficient,
      generatorDegree, koszulSign]
  all_goals norm_num
  all_goals
    simp [LambdaPolynomial.skew_single, smul_add, add_smul, smul_smul,
      Finset.sum_range_succ]
  all_goals simp only [← Finsupp.smul_single]
  all_goals module

private def expandLinear (r : ℕ) :
    LambdaPolynomial JetModule →ₗ[ℂ] TwoLambdaPolynomial JetModule :=
  Finsupp.lsum ℂ fun s =>
    ∑ i ∈ Finset.range (s + 1),
      (Nat.choose s i : ℂ) • Finsupp.lsingle (r + i, s - i)

private theorem expandLinear_apply (r : ℕ) (p : LambdaPolynomial JetModule) :
    expandLinear r p = p.sum (fun s v =>
      ∑ i ∈ Finset.range (s + 1),
        Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • v)) := by
  simp only [expandLinear, Finsupp.lsum_apply]
  apply Finsupp.sum_congr
  intro n _hn
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lsingle_apply,
    Finsupp.smul_single]

@[simp]
private theorem expandLinear_single (r s : ℕ) (v : JetModule) :
    expandLinear r (Finsupp.single s v) =
      ∑ i ∈ Finset.range (s + 1),
        Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • v) := by
  simp [expandLinear_apply]

private theorem binomial_sum_add (r : ℕ) (p q : LambdaPolynomial JetModule) :
    (p + q).sum (fun s v =>
      ∑ i ∈ Finset.range (s + 1),
        Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • v)) =
    p.sum (fun s v =>
      ∑ i ∈ Finset.range (s + 1),
        Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • v)) +
    q.sum (fun s v =>
      ∑ i ∈ Finset.range (s + 1),
        Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • v)) := by
  apply Finsupp.sum_add_index'
  · intro n
    simp
  · intro n u v
    simp [smul_add, Finsupp.single_add, Finset.sum_add_distrib]

private theorem middle_sum_add (br : LambdaBracket JetModule) (c : JetModule)
    (p q : LambdaPolynomial JetModule) :
    (p + q).sum (fun r ab =>
      (br ab c).sum fun s v =>
        ∑ i ∈ Finset.range (s + 1),
          Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • v)) =
    p.sum (fun r ab =>
      (br ab c).sum fun s v =>
        ∑ i ∈ Finset.range (s + 1),
          Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • v)) +
    q.sum (fun r ab =>
      (br ab c).sum fun s v =>
        ∑ i ∈ Finset.range (s + 1),
          Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • v)) := by
  apply Finsupp.sum_add_index'
  · intro n
    simp
  · intro n u v
    simp only [map_add, LinearMap.add_apply, binomial_sum_add]

set_option maxHeartbeats 1000000 in
theorem generator_super_jacobi (a b c : Kind) :
    jetBracket.jacobiLeft (jet a 0) (jet b 0) (jet c 0) =
      jetBracket.jacobiMiddle (jet a 0) (jet b 0) (jet c 0) +
        koszulSign (generatorDegree a) (generatorDegree b) •
          jetBracket.jacobiRight (jet a 0) (jet b 0) (jet c 0) := by
  cases a <;> cases b <;> cases c <;>
    simp only [LambdaBracket.jacobiLeft, LambdaBracket.jacobiMiddle,
      LambdaBracket.jacobiRight, ← expandLinear_apply, jetBracket_zero_zero,
      outputKind, derivativeCoefficient, variableCoefficient,
      generatorDegree, koszulSign]
  all_goals norm_num
  all_goals
    simp [middle_sum_add, binomial_sum_add,
      outputKind, derivativeCoefficient, variableCoefficient,
      Finsupp.sum_add_index, Finsupp.sum_neg_index, smul_add, add_smul, smul_smul, Finset.sum_range_succ,
      LinearMap.add_apply, LinearMap.smul_apply]
  all_goals simp only [← Finsupp.smul_single]
  all_goals module

end KhanSL2.SourceGeneratorChecks
