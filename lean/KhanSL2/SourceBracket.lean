module

public import KhanSL2.SourceHamiltonian
public import KhanSL2.SourceBracketOperators
public import KhanSL2.SourceBracketOperatorCalculus
public import KhanSL2.SourceParityProjections

@[expose] public section

/-! Construction of the left argument of the source lambda bracket. -/

noncomputable section

namespace KhanSL2.Source

open SourcePresentation LambdaPolynomial

attribute [local instance] FreeAlgebra.Pre.hasCoeGenerator
  FreeAlgebra.Pre.hasCoeSemiring FreeAlgebra.Pre.hasMul
  FreeAlgebra.Pre.hasAdd FreeAlgebra.Pre.hasZero FreeAlgebra.Pre.hasOne
  FreeAlgebra.Pre.hasSMul

abbrev BracketAction := Source →ₗ[ℂ] LambdaPolynomial Source

namespace BracketAction

open SourceBracketOperators

def leftAction (a : Source) (m : BracketAction) : BracketAction :=
  (left a).comp m

def rightAction (m : BracketAction) (b : Source) : BracketAction :=
  (right b).comp (m.comp evenPart) +
    (right (parity b)).comp (m.comp oddPart)

@[simp] theorem leftAction_apply (a : Source) (m : BracketAction) (c : Source) :
    leftAction a m c = left a (m c) := rfl

@[simp] theorem rightAction_apply (m : BracketAction) (b c : Source) :
    rightAction m b c =
      right b (m (evenPart c)) + right (parity b) (m (oddPart c)) := rfl

@[simp] theorem leftAction_zero (a : Source) : leftAction a 0 = 0 := by
  ext c
  simp

@[simp] theorem zero_leftAction (m : BracketAction) : leftAction 0 m = 0 := by
  ext c
  simp

@[simp] theorem rightAction_zero (b : Source) : rightAction 0 b = 0 := by
  ext c
  simp

@[simp] theorem zero_rightAction (m : BracketAction) : rightAction m 0 = 0 := by
  ext c
  simp

@[simp] theorem one_leftAction (m : BracketAction) : leftAction 1 m = m := by
  ext c
  simp

@[simp] theorem one_rightAction (m : BracketAction) : rightAction m 1 = m := by
  ext c
  simp only [rightAction_apply, map_one, right_one, Module.End.one_apply]
  rw [← map_add, evenPart_add_oddPart]

theorem leftAction_add (a : Source) (m n : BracketAction) :
    leftAction a (m + n) = leftAction a m + leftAction a n := by
  ext c
  simp

theorem add_leftAction (a b : Source) (m : BracketAction) :
    leftAction (a + b) m = leftAction a m + leftAction b m := by
  ext c
  simp [left_add]

theorem rightAction_add (m n : BracketAction) (b : Source) :
    rightAction (m + n) b = rightAction m b + rightAction n b := by
  ext c
  simp
  abel

theorem add_rightAction (m : BracketAction) (a b : Source) :
    rightAction m (a + b) = rightAction m a + rightAction m b := by
  ext c
  simp [right_add]
  abel

theorem mul_leftAction (a b : Source) (m : BracketAction) :
    leftAction (a * b) m = leftAction a (leftAction b m) := by
  ext c
  simp [left_mul, Module.End.mul_apply]

theorem mul_rightAction (m : BracketAction) (a b : Source) :
    rightAction m (a * b) = rightAction (rightAction m a) b := by
  ext c
  simp [right_mul, Module.End.mul_apply]

theorem leftAction_rightAction (a b : Source) (m : BracketAction) :
    leftAction a (rightAction m b) = rightAction (leftAction a m) b := by
  ext c
  simp only [leftAction_apply, rightAction_apply, map_add]
  have h (v : Source) (p : LambdaPolynomial Source) :
      left a (right v p) = right v (left a p) :=
    congrArg (fun f : SourceBracketOperators.Operator => f p) (left_right_commute a v)
  rw [h, h]

theorem scalar_leftAction (r : ℂ) (m : BracketAction) :
    leftAction (algebraMap ℂ Source r) m = r • m := by
  ext c
  simp [Algebra.algebraMap_eq_smul_one, left_smul]

theorem scalar_rightAction (r : ℂ) (m : BracketAction) :
    rightAction m (algebraMap ℂ Source r) = r • m := by
  apply LinearMap.ext
  intro c
  simp only [rightAction_apply, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    map_smul, map_one, right_smul, right_one, LinearMap.smul_apply, Module.End.one_apply]
  rw [← smul_add, ← map_add, evenPart_add_oddPart]

def translated (m : BracketAction) : BracketAction :=
  negativeShift.comp m

@[simp] theorem translated_apply (m : BracketAction) (c : Source) :
    translated m c = negativeShift (m c) := rfl

@[simp] theorem translated_zero : translated 0 = 0 := by
  ext c
  simp

theorem translated_add (m n : BracketAction) :
    translated (m + n) = translated m + translated n := by
  ext c
  simp

theorem translated_leftAction (a : Source) (m : BracketAction) :
    translated (leftAction a m) =
      leftAction (translation a) m + leftAction a (translated m) := by
  apply LinearMap.ext
  intro c
  exact left_translation_commutator a (m c)

theorem translated_rightAction (m : BracketAction) (a : Source) :
    translated (rightAction m a) =
      rightAction m (translation a) + rightAction (translated m) a := by
  ext c
  simp only [translated_apply, rightAction_apply, map_add, LinearMap.add_apply,
    right_translation_commutator, parity_translation]
  abel

end BracketAction

open BracketAction

/-- Raw first-slot extension. Its second argument is already an element of the
actual source quotient. -/
def rawBracket : Expression → BracketAction
  | .of (.X i) => (SourceBracketOperators.negativeShift ^ i).comp DX
  | .of (.Y i) => (SourceBracketOperators.negativeShift ^ i).comp DY
  | .ofScalar _ => 0
  | .add a b => rawBracket a + rawBracket b
  | .mul a b =>
      rightAction (rawBracket a) (mk b) + leftAction (mk a) (rawBracket b)

@[simp] theorem rawBracket_scalar (r : ℂ) : rawBracket (.ofScalar r) = 0 := rfl
@[simp] theorem rawBracket_zero : rawBracket 0 = 0 := rfl
@[simp] theorem rawBracket_one : rawBracket 1 = 0 := rfl
@[simp] theorem rawBracket_add (a b : Expression) :
    rawBracket (a + b) = rawBracket a + rawBracket b := rfl
@[simp] theorem rawBracket_mul (a b : Expression) :
    rawBracket (a * b) =
      rightAction (rawBracket a) (mk b) + leftAction (mk a) (rawBracket b) := rfl

theorem rawBracket_smul (r : ℂ) (a : Expression) :
    rawBracket (r • a) = r • rawBracket a := by
  change rightAction 0 (mk a) +
    leftAction (algebraMap ℂ Source r) (rawBracket a) = _
  simp [scalar_leftAction]

theorem rawBracket_algebra {a b : Expression}
    (h : FreeAlgebra.Rel ℂ Generator a b) : rawBracket a = rawBracket b := by
  induction h with
  | @add_compat_left a b c _ ih => simp only [rawBracket_add, ih]
  | @add_compat_right a b c _ ih => simp only [rawBracket_add, ih]
  | @mul_compat_left a b c h ih =>
    have hm : mk a = mk b := Quot.sound (Relation.algebra h)
    simp only [rawBracket_mul, ih, hm]
  | @mul_compat_right a b c h ih =>
    have hm : mk a = mk b := Quot.sound (Relation.algebra h)
    simp only [rawBracket_mul, ih, hm]
  | central_scalar =>
    simp [rawBracket_mul, scalar_leftAction, scalar_rightAction]
  | _ =>
    simp [rawBracket, mk_zero, mk_one, mk_add, mk_mul, mk_scalar,
      leftAction_add, add_leftAction, rightAction_add, add_rightAction,
      mul_leftAction, mul_rightAction, leftAction_rightAction,
      add_assoc, add_comm, add_left_comm]

theorem rawBracket_translate (a : Expression) :
    rawBracket (SourcePresentation.translate a) = translated (rawBracket a) := by
  induction a with
  | of g =>
    cases g with
    | X i =>
      ext c
      simp [SourcePresentation.translate, x, rawBracket, translated,
        pow_succ', LinearMap.comp_apply, Module.End.mul_apply]
    | Y i =>
      ext c
      simp [SourcePresentation.translate, y, rawBracket, translated,
        pow_succ', LinearMap.comp_apply, Module.End.mul_apply]
  | ofScalar _ => simp [SourcePresentation.translate]
  | add a b ha hb =>
    change rawBracket (SourcePresentation.translate a + SourcePresentation.translate b) =
      translated (rawBracket (a + b))
    simp only [rawBracket_add, ha, hb, translated_add]
  | mul a b ha hb =>
    change rawBracket (SourcePresentation.translate a * b + a * SourcePresentation.translate b) =
      translated (rawBracket (a * b))
    simp only [rawBracket_add, rawBracket_mul, ha, hb,
      mk_translate, translated_add, translated_leftAction, translated_rightAction]
    abel

open SourceBracketOperators

private theorem negativeShift_rightTranslation (p : LambdaPolynomial Source) :
    negativeShift (rightTranslation translation p) =
      rightTranslation translation (negativeShift p) := by
  simp [negativeShift_apply, rightTranslation_apply, mapCoefficients_shift]
  abel

private theorem negativeShift_pow_rightTranslation (n : ℕ)
    (p : LambdaPolynomial Source) :
    (negativeShift ^ n) (rightTranslation translation p) =
      rightTranslation translation ((negativeShift ^ n) p) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', Module.End.mul_apply, hn, negativeShift_rightTranslation,
      Module.End.mul_apply]

/-- Every raw first-slot action satisfies right sesquilinearity on the
actual source quotient. -/
theorem rawBracket_right_translation (a : Expression) (c : Source) :
    rawBracket a (translation c) =
      rightTranslation translation (rawBracket a c) := by
  induction a generalizing c with
  | of g =>
    cases g with
    | X i =>
      change (negativeShift ^ i) (DX (translation c)) =
        rightTranslation translation ((negativeShift ^ i) (DX c))
      rw [DX_translation, negativeShift_pow_rightTranslation]
    | Y i =>
      change (negativeShift ^ i) (DY (translation c)) =
        rightTranslation translation ((negativeShift ^ i) (DY c))
      rw [DY_translation, negativeShift_pow_rightTranslation]
  | ofScalar _ => simp [rawBracket]
  | add a b ha hb =>
    change (rawBracket (a + b)) (translation c) =
      rightTranslation translation (rawBracket (a + b) c)
    simp [ha, hb]
  | mul a b ha hb =>
    change (rawBracket (a * b)) (translation c) =
      rightTranslation translation (rawBracket (a * b) c)
    simp [evenPart_translation, oddPart_translation, ha, hb,
      rightTranslation_left, rightTranslation_right]

private theorem K_jetAction (g : ℕ → Source) (a b : ℂ) (i : ℕ) :
    K (jetAction g a b i) =
      (negativeShift ^ i) (K (jetAction g a b 0)) := by
  induction i with
  | zero => simp
  | succ i hi =>
    rw [jetAction_succ, K_rightTranslation, hi, pow_succ', Module.End.mul_apply]

private theorem K_XX_zero : K (XX 0) = -(XX 0) := by
  simp [XX, jetAction, K_apply, skew_single, Finset.sum_range_succ, smul_add,
    smul_smul]
  simp only [← Finsupp.smul_single]
  module

private theorem K_XY_zero : K (XY 0) = -(YX 0) := by
  simp [XX, XY, YX, jetAction, K_apply, skew_single, Finset.sum_range_succ,
    smul_add, smul_smul]
  simp only [← Finsupp.smul_single]
  module

private theorem K_YX_zero : K (YX 0) = -(XY 0) := by
  simp [XX, XY, YX, jetAction, K_apply, skew_single, Finset.sum_range_succ,
    smul_add, smul_smul]
  simp only [← Finsupp.smul_single]
  module

/-- The left raw extension already agrees with skew symmetry whenever its
right argument is the undifferentiated even generator. -/
theorem rawBracket_X0 (a : Expression) :
    rawBracket a (X 0) = -K (DX (mk a)) := by
  induction a with
  | of g =>
    cases g with
    | X i =>
      change (negativeShift ^ i) (XX 0) = -K (XX i)
      rw [show XX i = jetAction X 1 2 i from rfl, K_jetAction,
        show jetAction X 1 2 0 = XX 0 from rfl, K_XX_zero]
      simp
    | Y i =>
      change (negativeShift ^ i) (YX 0) = -K (XY i)
      rw [show XY i = jetAction Y 1 3 i from rfl, K_jetAction,
        show jetAction Y 1 3 0 = XY 0 from rfl, K_XY_zero]
      simp
  | ofScalar _ =>
    change 0 = -K 0
    simp
  | add a b ha hb =>
    change rawBracket (a + b) (X 0) = -K (DX (mk (a + b)))
    simp [ha, hb]
    abel
  | mul a b ha hb =>
    change rawBracket (a * b) (X 0) = -K (DX (mk (a * b)))
    simp only [rawBracket_mul, LinearMap.add_apply, rightAction_apply,
      evenPart_X, oddPart_X, map_zero, add_zero, leftAction_apply, ha, hb,
      mk_mul, DX_mul, right_apply, left_apply, map_neg, K_K, map_add, neg_add_rev]
    abel

/-- The corresponding odd-generator skew formula, valid for every raw first
expression and expressed entirely in terms of its source quotient class. -/
theorem rawBracket_Y0 (a : Expression) :
    rawBracket a (Y 0) = -K (DY (parity (mk a))) := by
  induction a with
  | of g =>
    cases g with
    | X i =>
      change (negativeShift ^ i) (XY 0) = -K (DY (parity (X i)))
      rw [parity_X, DY_X, show YX i = jetAction Y 2 3 i from rfl, K_jetAction,
        show jetAction Y 2 3 0 = YX 0 from rfl, K_YX_zero]
      simp
    | Y i =>
      change (negativeShift ^ i) (DY (Y 0)) = -K (DY (parity (Y i)))
      simp
  | ofScalar r =>
    rw [mk_scalar, parity.commutes]
    change 0 = -K 0
    simp
  | add a b ha hb =>
    change rawBracket (a + b) (Y 0) = -K (DY (parity (mk (a + b))))
    simp [ha, hb]
    abel
  | mul a b ha hb =>
    change rawBracket (a * b) (Y 0) = -K (DY (parity (mk (a * b))))
    simp only [rawBracket_mul, LinearMap.add_apply, rightAction_apply,
      evenPart_Y, oddPart_Y, map_zero, zero_add, leftAction_apply, ha, hb,
      mk_mul, map_mul, DY_mul, parity_parity, right_apply, left_apply,
      map_neg, K_K, map_add, neg_add_rev]
    abel

end KhanSL2.Source
