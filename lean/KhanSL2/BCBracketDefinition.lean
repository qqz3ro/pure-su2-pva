module

public import KhanSL2.BCModeKernel
public import KhanSL2.LambdaPolynomialSkew

@[expose] public section

/-!
# The actual finite-mode `bc` bracket

This is a concrete bilinear operation on the existing finite exterior-monomial
cochain space. No structural property or PVA bracket is assumed in defining it.
-/

noncomputable section

namespace KhanSL2.BC

open LambdaPolynomial

abbrev monomial (s : ExteriorMonomial) : Cochain := Finsupp.single s 1

/-- The bracket of one odd jet generator with an exterior monomial. -/
def generatorActionMonomial (m : Mode) (s : ExteriorMonomial) :
    LambdaPolynomial Cochain :=
  ∑ n ∈ s, ((-1 : ℂ) ^ position n s) •
    Finsupp.single (m.order + n.order)
      (kernelCoefficient m n • monomial (s.erase n))

/-- Right extension of the generator Hamiltonian as a linear map. -/
def generatorAction (m : Mode) : Cochain →ₗ[ℂ] LambdaPolynomial Cochain :=
  Finsupp.linearCombination ℂ (generatorActionMonomial m)

/-- Super-skew determines the bracket with an odd generator in its second slot. -/
def monomialGeneratorAction (s : ExteriorMonomial) (n : Mode) :
    LambdaPolynomial Cochain :=
  ((-1 : ℂ) ^ (s.card + 1)) •
    minusVariableMinusTranslation translation (generatorActionMonomial n s)

/-- The finite Wick-contraction formula on pairs of exterior monomials. -/
def monomialBracket (s t : ExteriorMonomial) : LambdaPolynomial Cochain :=
  ∑ n ∈ t, ((-1 : ℂ) ^ position n t) •
    mulRight cochainData (monomialGeneratorAction s n) (monomial (t.erase n))

/-- The normalized `bc` lambda bracket, on exactly the cochains used in the
relative CE complex. -/
def bracket : LambdaBracket Cochain :=
  Finsupp.linearCombination ℂ fun s =>
    Finsupp.linearCombination ℂ (monomialBracket s)

@[simp] theorem generatorAction_single (m : Mode) (s : ExteriorMonomial) (r : ℂ) :
    generatorAction m (Finsupp.single s r) = r • generatorActionMonomial m s := by
  simp [generatorAction]

@[simp] theorem bracket_single (s t : ExteriorMonomial) (r u : ℂ) :
    bracket (Finsupp.single s r) (Finsupp.single t u) =
      (r * u) • monomialBracket s t := by
  simp [bracket, smul_smul]

@[simp] theorem generatorActionMonomial_empty (m : Mode) :
    generatorActionMonomial m ∅ = 0 := by
  simp [generatorActionMonomial]

@[simp] theorem monomialBracket_empty_left (s : ExteriorMonomial) :
    monomialBracket ∅ s = 0 := by
  simp [monomialBracket, monomialGeneratorAction]

@[simp] theorem monomialBracket_empty_right (s : ExteriorMonomial) :
    monomialBracket s ∅ = 0 := by
  simp [monomialBracket]

@[simp] theorem bracket_one_left (u : Cochain) : bracket cochainOne u = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single s r => simp [cochainOne]

@[simp] theorem bracket_one_right (u : Cochain) : bracket u cochainOne = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single s r => simp [cochainOne]

private theorem translation_unit : translation cochainOne = 0 := by
  simp [translation, extendDerivation, cochainOne]

theorem skew_single_constant (f : Module.End ℂ Cochain) (a : Cochain)
    (ha : f a = 0) (n : ℕ) :
    minusVariableMinusTranslation f (Finsupp.single n a) =
      Finsupp.single n ((-1 : ℂ) ^ n • a) := by
  induction n with
  | zero => simp [skew_single]
  | succ n hn =>
    rw [skew_single_succ, hn]
    simp [ha, pow_succ, neg_smul, mul_smul]

theorem skew_kernel (m n : Mode) :
    minusVariableMinusTranslation translation (kernel n m) = kernel m n := by
  rw [kernel, skew_single_constant translation _ (by simp [translation_unit])]
  rw [kernel, smul_smul, Nat.add_comm n.order m.order, ← kernelCoefficient_swap]

@[simp] theorem generatorActionMonomial_singleton (m n : Mode) :
    generatorActionMonomial m {n} = kernel m n := by
  have h : ({n} : Finset Mode).filter (fun a => a.code < n.code) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha
    simpa only [Finset.mem_singleton.mp ha] using Nat.lt_irrefl n.code
  simp [generatorActionMonomial, position, h, kernel, cochainOne]

@[simp] theorem monomialGeneratorAction_singleton (m n : Mode) :
    monomialGeneratorAction {m} n = kernel m n := by
  simp [monomialGeneratorAction, skew_kernel]

private theorem wedge_unit_right (u : Cochain) : wedge u cochainOne = u := by
  induction u using Finsupp.induction_linear with
  | zero => simp [wedge]
  | add u v hu hv =>
    simp only [wedge, map_add, LinearMap.add_apply]
    change wedge u cochainOne + wedge v cochainOne = u + v
    rw [hu, hv]
  | single s r =>
    simp [wedge, wedgeLinear, cochainOne, monomialWedge, inversionCount]

@[simp] theorem bracket_generator (m n : Mode) :
    bracket (generator m) (generator n) = kernel m n := by
  have h : ({n} : Finset Mode).filter (fun a => a.code < n.code) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro a ha
    simpa only [Finset.mem_singleton.mp ha] using Nat.lt_irrefl n.code
  simp only [generator, bracket_single, one_mul, one_smul, monomialBracket,
    Finset.sum_singleton, position, h, Finset.card_empty, pow_zero, one_smul,
    Finset.erase_singleton, monomialGeneratorAction_singleton]
  change mulRight cochainData (kernel m n) cochainOne = _
  rw [kernel, mulRight_single]
  change Finsupp.single _ (wedge _ cochainOne) = _
  rw [wedge_unit_right]

/-- The fixed, explicitly constructed bracket has exactly the requested
normalization on all finite modes. -/
theorem bracket_isBCBracket : IsBCBracket bracket where
  bb j k a b := by simp
  cc j k a b := by simp
  bc j k a b := by simpa only [bracket_generator] using kernel_bc j k a b

@[simp] theorem bracket_generator_jacobiLeft (m n p : Mode) :
    bracket.jacobiLeft (generator m) (generator n) (generator p) = 0 := by
  simp [LambdaBracket.jacobiLeft, kernel]

@[simp] theorem bracket_generator_jacobiMiddle (m n p : Mode) :
    bracket.jacobiMiddle (generator m) (generator n) (generator p) = 0 := by
  simp [LambdaBracket.jacobiMiddle, kernel]

@[simp] theorem bracket_generator_jacobiRight (m n p : Mode) :
    bracket.jacobiRight (generator m) (generator n) (generator p) = 0 := by
  simp [LambdaBracket.jacobiRight, kernel]

theorem bracket_generator_super_jacobi (m n p : Mode) :
    bracket.jacobiLeft (generator m) (generator n) (generator p) =
      bracket.jacobiMiddle (generator m) (generator n) (generator p) -
        bracket.jacobiRight (generator m) (generator n) (generator p) := by
  simp

end KhanSL2.BC
