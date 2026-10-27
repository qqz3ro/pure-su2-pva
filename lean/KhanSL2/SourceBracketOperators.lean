module

public import KhanSL2.SourceData
public import KhanSL2.SourceParity
public import KhanSL2.LambdaPolynomialSkew

@[expose] public section

/-!
# The coefficient multiplication operators in the left PVA Leibniz rule

Conjugating left and right coefficient multiplication by skew substitution
gives commuting module actions. All identities below are actual equalities of
linear maps on the fixed source polynomial space.
-/

noncomputable section

namespace KhanSL2.SourceBracketOperators

open LambdaPolynomial

abbrev Poly := LambdaPolynomial Source
abbrev Operator := Module.End ℂ Poly

def K : Operator := skewLinear Source.translation

theorem K_apply (p : Poly) :
    K p = minusVariableMinusTranslation Source.translation p :=
  skewLinear_apply _ _

@[simp] theorem K_K (p : Poly) : K (K p) = p := by
  simp only [K_apply, skew_involutive]

def conjugate (f : Operator) : Operator := K.comp (f.comp K)

@[simp] theorem conjugate_apply (f : Operator) (p : Poly) :
    conjugate f p = K (f (K p)) := rfl

@[simp] theorem conjugate_zero : conjugate 0 = 0 := by
  ext p
  simp

@[simp] theorem conjugate_one : conjugate 1 = 1 := by
  ext p
  simp

theorem conjugate_add (f g : Operator) :
    conjugate (f + g) = conjugate f + conjugate g := by
  ext p
  simp

theorem conjugate_smul (r : ℂ) (f : Operator) :
    conjugate (r • f) = r • conjugate f := by
  ext p
  simp

theorem conjugate_mul (f g : Operator) :
    conjugate (f * g) = conjugate f * conjugate g := by
  apply LinearMap.ext
  intro p
  change K (f (g (K p))) = K (f (K (K (g (K p)))))
  rw [K_K]

@[simp] theorem conjugate_conjugate (f : Operator) :
    conjugate (conjugate f) = f := by
  ext p
  simp

def left (a : Source) : Operator := conjugate (mulLeftLinear sourceData a)
def right (a : Source) : Operator := conjugate (mulRightLinear sourceData a)

theorem left_apply (a : Source) (p : Poly) :
    left a p = K (mulLeft sourceData a (K p)) := rfl

theorem right_apply (a : Source) (p : Poly) :
    right a p = K (mulRight sourceData (K p) a) := rfl

@[simp] theorem left_zero : left 0 = 0 := by
  have h : mulLeftLinear sourceData 0 = 0 := by
    ext p n
    simp [mulLeftLinear_apply, sourceData]
  rw [left, h, conjugate_zero]

@[simp] theorem right_zero : right 0 = 0 := by
  have h : mulRightLinear sourceData 0 = 0 := by
    ext p n
    simp [mulRightLinear_apply, sourceData]
  rw [right, h, conjugate_zero]

@[simp] theorem left_one : left 1 = 1 := by
  have h : mulLeftLinear sourceData 1 = 1 := by
    ext p n
    simp [mulLeftLinear_apply, sourceData]
  rw [left, h, conjugate_one]

@[simp] theorem right_one : right 1 = 1 := by
  have h : mulRightLinear sourceData 1 = 1 := by
    ext p n
    simp [mulRightLinear_apply, sourceData]
  rw [right, h, conjugate_one]

theorem left_add (a b : Source) : left (a + b) = left a + left b := by
  have h : mulLeftLinear sourceData (a + b) =
      mulLeftLinear sourceData a + mulLeftLinear sourceData b := by
    ext p n
    simp [mulLeftLinear_apply, sourceData, add_mul]
  simp only [left, h, conjugate_add]

theorem right_add (a b : Source) : right (a + b) = right a + right b := by
  have h : mulRightLinear sourceData (a + b) =
      mulRightLinear sourceData a + mulRightLinear sourceData b := by
    ext p n
    simp [mulRightLinear_apply, sourceData, mul_add]
  simp only [right, h, conjugate_add]

theorem left_smul (r : ℂ) (a : Source) : left (r • a) = r • left a := by
  have h : mulLeftLinear sourceData (r • a) = r • mulLeftLinear sourceData a := by
    ext p n
    simp [mulLeftLinear_apply, sourceData]
  simp only [left, h, conjugate_smul]

theorem right_smul (r : ℂ) (a : Source) : right (r • a) = r • right a := by
  have h : mulRightLinear sourceData (r • a) = r • mulRightLinear sourceData a := by
    ext p n
    simp [mulRightLinear_apply, sourceData]
  simp only [right, h, conjugate_smul]

theorem left_mul (a b : Source) : left (a * b) = left a * left b := by
  have h : mulLeftLinear sourceData (a * b) =
      mulLeftLinear sourceData a * mulLeftLinear sourceData b := by
    ext p n
    simp [Module.End.mul_apply, mulLeftLinear_apply, sourceData, mul_assoc]
  simp only [left, h, conjugate_mul]

/-- Right multiplication has the reversed operator composition order. -/
theorem right_mul (a b : Source) : right (a * b) = right b * right a := by
  have h : mulRightLinear sourceData (a * b) =
      mulRightLinear sourceData b * mulRightLinear sourceData a := by
    ext p n
    simp [Module.End.mul_apply, mulRightLinear_apply, sourceData, mul_assoc]
  simp only [right, h, conjugate_mul]

theorem left_right_commute (a b : Source) :
    left a * right b = right b * left a := by
  have h : mulLeftLinear sourceData a * mulRightLinear sourceData b =
      mulRightLinear sourceData b * mulLeftLinear sourceData a := by
    ext p n
    simp [Module.End.mul_apply, mulRightLinear_apply, mulLeftLinear_apply,
      sourceData, mul_assoc]
  simp only [left, right, ← conjugate_mul, h]

def negativeShift : Operator := -shiftLinear

theorem negativeShift_apply (p : Poly) : negativeShift p = -shift p := rfl

theorem K_rightTranslation (p : Poly) :
    K (rightTranslation Source.translation p) = negativeShift (K p) := by
  simp only [rightTranslation_apply, negativeShift_apply, K_apply, skew_add,
    skew_mapCoefficients, skew_shift]
  abel

theorem rightTranslation_K (p : Poly) :
    rightTranslation Source.translation (K p) = K (negativeShift p) := by
  have h := K_rightTranslation (K p)
  have h' := congrArg K h
  simpa only [K_K] using h'

theorem left_translation_commutator (a : Source) (p : Poly) :
    negativeShift (left a p) =
      left (Source.translation a) p + left a (negativeShift p) := by
  rw [left_apply, ← K_rightTranslation]
  have h := rightTranslation_mulLeft sourceData Source.translation_mul a (K p)
  change rightTranslation Source.translation (mulLeft sourceData a (K p)) =
    mulLeft sourceData (Source.translation a) (K p) +
      mulLeft sourceData a (rightTranslation Source.translation (K p)) at h
  rw [h, map_add, rightTranslation_K]
  rfl

theorem right_translation_commutator (a : Source) (p : Poly) :
    negativeShift (right a p) =
      right (Source.translation a) p + right a (negativeShift p) := by
  rw [right_apply, ← K_rightTranslation]
  have h := rightTranslation_mulRight sourceData Source.translation_mul (K p) a
  change rightTranslation Source.translation (mulRight sourceData (K p) a) =
    mulRight sourceData (rightTranslation Source.translation (K p)) a +
      mulRight sourceData (K p) (Source.translation a) at h
  rw [h, map_add, rightTranslation_K, add_comm]
  rfl

end KhanSL2.SourceBracketOperators
