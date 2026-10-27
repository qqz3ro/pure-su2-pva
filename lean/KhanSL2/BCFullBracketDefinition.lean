module

public import KhanSL2.BCFullKernel
public import KhanSL2.LambdaPolynomialSkew

@[expose] public section

/-!
# The finite-mode `bc` bracket with zero ghosts

This is a concrete bilinear operation on the finite exterior-monomial space
including all three zero ghosts. No structural property or PVA bracket is
assumed in defining it.
-/

noncomputable section

namespace KhanSL2.FullBC

open LambdaPolynomial

def fullPosition (m : FullMode) (s : FullExteriorMonomial) : ℕ :=
  FiniteExterior.position FullMode.code m s

abbrev monomial (s : FullExteriorMonomial) : FullCochain := Finsupp.single s 1

/-- The bracket of one odd jet fullGenerator with an exterior monomial. -/
def generatorActionMonomial (m : FullMode) (s : FullExteriorMonomial) :
    LambdaPolynomial FullCochain :=
  ∑ n ∈ s, ((-1 : ℂ) ^ fullPosition n s) •
    Finsupp.single (m.order + n.order)
      (kernelCoefficient m n • monomial (s.erase n))

/-- Right extension of the fullGenerator Hamiltonian as a linear map. -/
def generatorAction (m : FullMode) : FullCochain →ₗ[ℂ] LambdaPolynomial FullCochain :=
  Finsupp.linearCombination ℂ (generatorActionMonomial m)

/-- Super-skew determines the bracket with an odd fullGenerator in its second slot. -/
def monomialGeneratorAction (s : FullExteriorMonomial) (n : FullMode) :
    LambdaPolynomial FullCochain :=
  ((-1 : ℂ) ^ (s.card + 1)) •
    minusVariableMinusTranslation fullTranslation (generatorActionMonomial n s)

/-- The finite Wick-contraction formula on pairs of exterior monomials. -/
def monomialBracket (s t : FullExteriorMonomial) : LambdaPolynomial FullCochain :=
  ∑ n ∈ t, ((-1 : ℂ) ^ fullPosition n t) •
    mulRight fullData (monomialGeneratorAction s n) (monomial (t.erase n))

/-- The normalized `bc` lambda bracket after adjoining the zero ghosts. -/
def bracket : LambdaBracket FullCochain :=
  Finsupp.linearCombination ℂ fun s =>
    Finsupp.linearCombination ℂ (monomialBracket s)

@[simp] theorem generatorAction_single (m : FullMode) (s : FullExteriorMonomial) (r : ℂ) :
    generatorAction m (Finsupp.single s r) = r • generatorActionMonomial m s := by
  simp [generatorAction]

@[simp] theorem bracket_single (s t : FullExteriorMonomial) (r u : ℂ) :
    bracket (Finsupp.single s r) (Finsupp.single t u) =
      (r * u) • monomialBracket s t := by
  simp [bracket, smul_smul]

@[simp] theorem generatorActionMonomial_empty (m : FullMode) :
    generatorActionMonomial m ∅ = 0 := by
  simp [generatorActionMonomial]

@[simp] theorem monomialBracket_empty_left (s : FullExteriorMonomial) :
    monomialBracket ∅ s = 0 := by
  simp [monomialBracket, monomialGeneratorAction]

@[simp] theorem monomialBracket_empty_right (s : FullExteriorMonomial) :
    monomialBracket s ∅ = 0 := by
  simp [monomialBracket]

@[simp] theorem bracket_one_left (u : FullCochain) : bracket fullOne u = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single s r => simp [fullOne, FiniteExterior.monomial]

@[simp] theorem bracket_one_right (u : FullCochain) : bracket u fullOne = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single s r => simp [fullOne, FiniteExterior.monomial]

private theorem translation_unit : fullTranslation fullOne = 0 := by
  simp [fullTranslation, FiniteExterior.extendDerivation, fullOne, FiniteExterior.monomial]

theorem skew_single_constant (f : Module.End ℂ FullCochain) (a : FullCochain)
    (ha : f a = 0) (n : ℕ) :
    minusVariableMinusTranslation f (Finsupp.single n a) =
      Finsupp.single n ((-1 : ℂ) ^ n • a) := by
  induction n with
  | zero => simp [skew_single]
  | succ n hn =>
    rw [skew_single_succ, hn]
    simp [ha, pow_succ, neg_smul, mul_smul]

theorem skew_kernel (m n : FullMode) :
    minusVariableMinusTranslation fullTranslation (kernel n m) = kernel m n := by
  rw [kernel, skew_single_constant fullTranslation _ (by simp [translation_unit])]
  rw [kernel, smul_smul, Nat.add_comm n.order m.order, ← kernelCoefficient_swap]

@[simp] theorem generatorActionMonomial_singleton (m n : FullMode) :
    generatorActionMonomial m {n} = kernel m n := by
  have h : ({n} : Finset FullMode).filter (fun a => a.code < n.code) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha
    simpa only [Finset.mem_singleton.mp ha] using Nat.lt_irrefl n.code
  simp [generatorActionMonomial, fullPosition, FiniteExterior.position,
    h, kernel, fullOne, FiniteExterior.monomial]

@[simp] theorem monomialGeneratorAction_singleton (m n : FullMode) :
    monomialGeneratorAction {m} n = kernel m n := by
  simp [monomialGeneratorAction, skew_kernel]

private theorem wedge_unit_right (u : FullCochain) : fullWedge u fullOne = u :=
  FiniteExterior.wedge_one_right FullMode.code u

@[simp] theorem bracket_generator (m n : FullMode) :
    bracket (fullGenerator m) (fullGenerator n) = kernel m n := by
  have h : ({n} : Finset FullMode).filter (fun a => a.code < n.code) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha
    simpa only [Finset.mem_singleton.mp ha] using Nat.lt_irrefl n.code
  simp only [fullGenerator, FiniteExterior.generator, FiniteExterior.monomial,
    bracket_single, one_mul, one_smul, monomialBracket,
    Finset.sum_singleton, fullPosition, FiniteExterior.position,
    h, Finset.card_empty, pow_zero, one_smul,
    Finset.erase_singleton, monomialGeneratorAction_singleton]
  change mulRight fullData (kernel m n) fullOne = _
  rw [kernel, mulRight_single]
  change Finsupp.single _ (fullWedge _ fullOne) = _
  rw [wedge_unit_right]

@[simp] theorem bracket_generator_jacobiLeft (m n p : FullMode) :
    bracket.jacobiLeft (fullGenerator m) (fullGenerator n) (fullGenerator p) = 0 := by
  simp [LambdaBracket.jacobiLeft, kernel]

@[simp] theorem bracket_generator_jacobiMiddle (m n p : FullMode) :
    bracket.jacobiMiddle (fullGenerator m) (fullGenerator n) (fullGenerator p) = 0 := by
  simp [LambdaBracket.jacobiMiddle, kernel]

@[simp] theorem bracket_generator_jacobiRight (m n p : FullMode) :
    bracket.jacobiRight (fullGenerator m) (fullGenerator n) (fullGenerator p) = 0 := by
  simp [LambdaBracket.jacobiRight, kernel]

theorem bracket_generator_super_jacobi (m n p : FullMode) :
    bracket.jacobiLeft (fullGenerator m) (fullGenerator n) (fullGenerator p) =
      bracket.jacobiMiddle (fullGenerator m) (fullGenerator n) (fullGenerator p) -
        bracket.jacobiRight (fullGenerator m) (fullGenerator n) (fullGenerator p) := by
  simp

end KhanSL2.FullBC

