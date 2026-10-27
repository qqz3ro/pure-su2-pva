module

public import KhanSL2.PVA
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.BilinearMap

@[expose] public section

/-! Linear algebra for the polynomial operations in the PVA definition. -/

noncomputable section

namespace KhanSL2.LambdaPolynomial

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

/-- Multiplication by lambda as a linear operator. -/
def shiftLinear : Module.End ℂ (LambdaPolynomial A) :=
  Finsupp.lsum ℂ fun n => Finsupp.lsingle (n + 1)

theorem shiftLinear_apply (p : LambdaPolynomial A) :
    shiftLinear p = shift p := rfl

@[simp] theorem shift_zero : shift (0 : LambdaPolynomial A) = 0 :=
  shiftLinear.map_zero

@[simp] theorem shift_add (p q : LambdaPolynomial A) :
    shift (p + q) = shift p + shift q :=
  shiftLinear.map_add p q

@[simp] theorem shift_smul (r : ℂ) (p : LambdaPolynomial A) :
    shift (r • p) = r • shift p :=
  shiftLinear.map_smul r p

@[simp] theorem shift_neg (p : LambdaPolynomial A) :
    shift (-p) = -shift p :=
  shiftLinear.map_neg p

omit [Module ℂ A] in
@[simp] theorem shift_single (n : ℕ) (a : A) :
    shift (Finsupp.single n a) = Finsupp.single (n + 1) a := by
  simp [shift]

/-- A coefficientwise linear operation, bundled as a linear map. -/
def coefficientsLinear (f : A →ₗ[ℂ] A) : Module.End ℂ (LambdaPolynomial A) :=
  Finsupp.lsum ℂ fun n => (Finsupp.lsingle n).comp f

theorem coefficientsLinear_apply (f : A →ₗ[ℂ] A) (p : LambdaPolynomial A) :
    coefficientsLinear f p = mapCoefficients f p := rfl

@[simp] theorem mapCoefficients_zero (f : A →ₗ[ℂ] A) :
    mapCoefficients f 0 = 0 :=
  (coefficientsLinear f).map_zero

@[simp] theorem mapCoefficients_add (f : A →ₗ[ℂ] A) (p q : LambdaPolynomial A) :
    mapCoefficients f (p + q) = mapCoefficients f p + mapCoefficients f q :=
  (coefficientsLinear f).map_add p q

@[simp] theorem mapCoefficients_smul (f : A →ₗ[ℂ] A) (r : ℂ)
    (p : LambdaPolynomial A) :
    mapCoefficients f (r • p) = r • mapCoefficients f p :=
  (coefficientsLinear f).map_smul r p

@[simp] theorem mapCoefficients_neg (f : A →ₗ[ℂ] A) (p : LambdaPolynomial A) :
    mapCoefficients f (-p) = -mapCoefficients f p :=
  (coefficientsLinear f).map_neg p

@[simp] theorem mapCoefficients_single (f : A →ₗ[ℂ] A) (n : ℕ) (a : A) :
    mapCoefficients f (Finsupp.single n a) = Finsupp.single n (f a) := by
  simp [mapCoefficients]

@[simp] theorem mapCoefficients_apply (f : A →ₗ[ℂ] A)
    (p : LambdaPolynomial A) (n : ℕ) :
    mapCoefficients f p n = f (p n) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single k a =>
    simp only [mapCoefficients_single]
    by_cases h : k = n
    · subst k; simp
    · simp [Finsupp.single_apply, h, Ne.symm h]

theorem mapCoefficients_shift (f : A →ₗ[ℂ] A) (p : LambdaPolynomial A) :
    mapCoefficients f (shift p) = shift (mapCoefficients f p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n a => simp

/-- The operator `partial + lambda` from right sesquilinearity. -/
def rightTranslation (f : Module.End ℂ A) : Module.End ℂ (LambdaPolynomial A) :=
  coefficientsLinear f + shiftLinear

theorem rightTranslation_apply (f : Module.End ℂ A) (p : LambdaPolynomial A) :
    rightTranslation f p = mapCoefficients f p + shift p := rfl

/-- The actual skew-substitution formula is linear in its polynomial input. -/
def skewLinear (f : Module.End ℂ A) : Module.End ℂ (LambdaPolynomial A) :=
  Finsupp.lsum ℂ fun n =>
    ∑ j ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ n * (Nat.choose n j : ℂ)) •
        ((Finsupp.lsingle j).comp (f ^ (n - j)))

theorem skewLinear_apply (f : Module.End ℂ A) (p : LambdaPolynomial A) :
    skewLinear f p = minusVariableMinusTranslation f p := by
  simp only [skewLinear, Finsupp.lsum_apply, minusVariableMinusTranslation]
  apply Finsupp.sum_congr
  intro n _hn
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Finsupp.lsingle_apply, Finsupp.smul_single]

@[simp] theorem skew_zero (f : Module.End ℂ A) :
    minusVariableMinusTranslation f 0 = 0 := by
  rw [← skewLinear_apply]
  exact (skewLinear f).map_zero

@[simp] theorem skew_add (f : Module.End ℂ A) (p q : LambdaPolynomial A) :
    minusVariableMinusTranslation f (p + q) =
      minusVariableMinusTranslation f p + minusVariableMinusTranslation f q := by
  simp only [← skewLinear_apply, map_add]

@[simp] theorem skew_smul (f : Module.End ℂ A) (r : ℂ) (p : LambdaPolynomial A) :
    minusVariableMinusTranslation f (r • p) =
      r • minusVariableMinusTranslation f p := by
  simp only [← skewLinear_apply, map_smul]

@[simp] theorem skew_neg (f : Module.End ℂ A) (p : LambdaPolynomial A) :
    minusVariableMinusTranslation f (-p) =
      -minusVariableMinusTranslation f p := by
  simp only [← skewLinear_apply, map_neg]

theorem skew_single (f : Module.End ℂ A) (n : ℕ) (a : A) :
    minusVariableMinusTranslation f (Finsupp.single n a) =
      ∑ j ∈ Finset.range (n + 1),
        Finsupp.single j
          (((-1 : ℂ) ^ n * (Nat.choose n j : ℂ)) • ((f ^ (n - j)) a)) := by
  simp [minusVariableMinusTranslation]

@[simp] theorem shift_apply_zero (p : LambdaPolynomial A) : shift p 0 = 0 := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n a => simp

@[simp] theorem shift_apply_succ (p : LambdaPolynomial A) (n : ℕ) :
    shift p (n + 1) = p n := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single k a => simp [Finsupp.single_apply]

def mulRightLinear (D : DifferentialData A) (b : A) :
    Module.End ℂ (LambdaPolynomial A) :=
  coefficientsLinear (D.mul.flip b)

def mulLeftLinear (D : DifferentialData A) (a : A) :
    Module.End ℂ (LambdaPolynomial A) :=
  coefficientsLinear (D.mul a)

theorem mulRightLinear_apply (D : DifferentialData A) (b : A)
    (p : LambdaPolynomial A) : mulRightLinear D b p = mulRight D p b := rfl

theorem mulLeftLinear_apply (D : DifferentialData A) (a : A)
    (p : LambdaPolynomial A) : mulLeftLinear D a p = mulLeft D a p := rfl

@[simp] theorem mulRight_apply (D : DifferentialData A) (p : LambdaPolynomial A)
    (b : A) (n : ℕ) : mulRight D p b n = D.mul (p n) b :=
  mapCoefficients_apply (D.mul.flip b) p n

@[simp] theorem mulLeft_apply (D : DifferentialData A) (a : A)
    (p : LambdaPolynomial A) (n : ℕ) : mulLeft D a p n = D.mul a (p n) :=
  mapCoefficients_apply (D.mul a) p n

@[simp] theorem mulRight_zero (D : DifferentialData A) (a : A) :
    mulRight D 0 a = 0 := (mulRightLinear D a).map_zero

@[simp] theorem mulLeft_zero (D : DifferentialData A) (a : A) :
    mulLeft D a 0 = 0 := (mulLeftLinear D a).map_zero

@[simp] theorem mulRight_add (D : DifferentialData A)
    (p q : LambdaPolynomial A) (a : A) :
    mulRight D (p + q) a = mulRight D p a + mulRight D q a :=
  (mulRightLinear D a).map_add p q

@[simp] theorem mulLeft_add (D : DifferentialData A) (a : A)
    (p q : LambdaPolynomial A) :
    mulLeft D a (p + q) = mulLeft D a p + mulLeft D a q :=
  (mulLeftLinear D a).map_add p q

@[simp] theorem mulRight_single (D : DifferentialData A)
    (n : ℕ) (a b : A) :
    mulRight D (Finsupp.single n a) b = Finsupp.single n (D.mul a b) :=
  mapCoefficients_single (D.mul.flip b) n a

@[simp] theorem mulLeft_single (D : DifferentialData A)
    (a : A) (n : ℕ) (b : A) :
    mulLeft D a (Finsupp.single n b) = Finsupp.single n (D.mul a b) :=
  mapCoefficients_single (D.mul a) n b

theorem rightTranslation_mulRight (D : DifferentialData A)
    (hD : ∀ a b, D.translation (D.mul a b) =
      D.mul (D.translation a) b + D.mul a (D.translation b))
    (p : LambdaPolynomial A) (b : A) :
    rightTranslation D.translation (mulRight D p b) =
      mulRight D (rightTranslation D.translation p) b +
        mulRight D p (D.translation b) := by
  ext n
  cases n with
  | zero =>
    simp [rightTranslation_apply, hD]
  | succ n =>
    simp [rightTranslation_apply, hD, add_assoc, add_left_comm, add_comm]

theorem rightTranslation_mulLeft (D : DifferentialData A)
    (hD : ∀ a b, D.translation (D.mul a b) =
      D.mul (D.translation a) b + D.mul a (D.translation b))
    (a : A) (p : LambdaPolynomial A) :
    rightTranslation D.translation (mulLeft D a p) =
      mulLeft D (D.translation a) p +
        mulLeft D a (rightTranslation D.translation p) := by
  ext n
  cases n with
  | zero =>
    simp [rightTranslation_apply, hD]
  | succ n =>
    simp [rightTranslation_apply, hD, add_assoc, add_left_comm, add_comm]

end KhanSL2.LambdaPolynomial
