module

public import KhanSL2.SourceJacobiExtension
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-! Translation of the finite bivariate Jacobi polynomials. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.LambdaBracket

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

def lambdaShift : Module.End ℂ (TwoLambdaPolynomial A) :=
  Finsupp.lsum ℂ fun ij => Finsupp.lsingle (ij.1 + 1, ij.2)

def muShift : Module.End ℂ (TwoLambdaPolynomial A) :=
  Finsupp.lsum ℂ fun ij => Finsupp.lsingle (ij.1, ij.2 + 1)

@[simp] theorem lambdaShift_single (i j : ℕ) (a : A) :
    lambdaShift (Finsupp.single (i, j) a) = Finsupp.single (i + 1, j) a := by
  change (Finsupp.single (i, j) a).sum
    (fun ij b => Finsupp.single (ij.1 + 1, ij.2) b) = _
  exact Finsupp.sum_single_index (by simp)

@[simp] theorem muShift_single (i j : ℕ) (a : A) :
    muShift (Finsupp.single (i, j) a) = Finsupp.single (i, j + 1) a := by
  change (Finsupp.single (i, j) a).sum
    (fun ij b => Finsupp.single (ij.1, ij.2 + 1) b) = _
  exact Finsupp.sum_single_index (by simp)

@[simp] theorem lambdaShift_pow_single (n i j : ℕ) (a : A) :
    (lambdaShift ^ n) (Finsupp.single (i, j) a) = Finsupp.single (i + n, j) a := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ih, Nat.add_assoc]

@[simp] theorem muShift_pow_single (n i j : ℕ) (a : A) :
    (muShift ^ n) (Finsupp.single (i, j) a) = Finsupp.single (i, j + n) a := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ih, Nat.add_assoc]

theorem shifts_commute :
    Commute (lambdaShift (A := A)) muShift := by
  apply LinearMap.ext
  intro p
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single ij a => rcases ij with ⟨i, j⟩; simp

theorem expand_single_eq_pow (r s : ℕ) (a : A) :
    expand r (Finsupp.single s a) =
      ((lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A)) ^ s)
        (Finsupp.single (r, 0) a) := by
  rw [shifts_commute.add_pow, LinearMap.sum_apply, expand_single]
  apply Finset.sum_congr rfl
  intro i _
  simp [Module.End.mul_apply, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]

/-- Substitution sends multiplication by the original variable to
multiplication by `lambda + mu`. -/
theorem expand_shift (r : ℕ) (p : LambdaPolynomial A) :
    expand r p.shift =
      (lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A)) (expand r p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [LambdaPolynomial.shift_add, map_add, hp, hq]
  | single s a =>
    rw [LambdaPolynomial.shift_single, expand_single_eq_pow, expand_single_eq_pow,
      pow_succ', Module.End.mul_apply]

theorem lambdaShift_coeff_zero (p : TwoLambdaPolynomial A) (j : ℕ) :
    lambdaShift p (0, j) = 0 := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single ij a => rcases ij with ⟨i, k⟩; simp [Finsupp.single_apply]

theorem lambdaShift_coeff_succ (p : TwoLambdaPolynomial A) (i j : ℕ) :
    lambdaShift p (i + 1, j) = p (i, j) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single ij a =>
    rcases ij with ⟨k, l⟩
    simp [Finsupp.single_apply]

theorem muShift_coeff_zero (p : TwoLambdaPolynomial A) (i : ℕ) :
    muShift p (i, 0) = 0 := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single ij a => rcases ij with ⟨k, j⟩; simp [Finsupp.single_apply]

theorem muShift_coeff_succ (p : TwoLambdaPolynomial A) (i j : ℕ) :
    muShift p (i, j + 1) = p (i, j) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single ij a =>
    rcases ij with ⟨k, l⟩
    simp [Finsupp.single_apply]

/-- The operator `partial + lambda + mu` on the Jacobi polynomial. -/
def jacobiTranslation (T : Module.End ℂ A) : Module.End ℂ (TwoLambdaPolynomial A) :=
  Finsupp.mapRange.linearMap T + lambdaShift + muShift

def HasSesquilinearRight (T : Module.End ℂ A) (br : LambdaBracket A) : Prop :=
  ∀ a b, br a (T b) = (br a b).mapCoefficients T + (br a b).shift

theorem mapCoefficients_eq_mapRange (T : Module.End ℂ A) (p : LambdaPolynomial A) :
    p.mapCoefficients T = Finsupp.mapRange.linearMap T p := by
  ext n
  simp

theorem jacobiLeft_translation {T : Module.End ℂ A} {br : LambdaBracket A}
    (hR : HasSesquilinearRight T br) (a b c : A) :
    jacobiLeft br a b (T c) = jacobiTranslation T (jacobiLeft br a b c) := by
  unfold HasSesquilinearRight at hR
  ext ⟨i, j⟩
  cases i <;> cases j <;>
    simp only [jacobiTranslation, LinearMap.add_apply, Finsupp.add_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, jacobiLeft_coeff,
      hR, lambdaShift_coeff_zero,
      lambdaShift_coeff_succ, muShift_coeff_zero, muShift_coeff_succ,
      LambdaPolynomial.mapCoefficients_apply, LambdaPolynomial.shift_apply_zero,
      LambdaPolynomial.shift_apply_succ, map_add, map_zero, Finsupp.zero_apply,
      zero_add, add_zero]

theorem jacobiRight_translation {T : Module.End ℂ A} {br : LambdaBracket A}
    (hR : HasSesquilinearRight T br) (a b c : A) :
    jacobiRight br a b (T c) = jacobiTranslation T (jacobiRight br a b c) := by
  unfold HasSesquilinearRight at hR
  ext ⟨i, j⟩
  cases i <;> cases j <;>
    simp only [jacobiTranslation, LinearMap.add_apply, Finsupp.add_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply, jacobiRight_coeff,
      hR, lambdaShift_coeff_zero,
      lambdaShift_coeff_succ, muShift_coeff_zero, muShift_coeff_succ,
      LambdaPolynomial.mapCoefficients_apply, LambdaPolynomial.shift_apply_zero,
      LambdaPolynomial.shift_apply_succ, map_add, map_zero, Finsupp.zero_apply,
      zero_add, add_zero]
  abel

theorem jacobiMiddle_translation {T : Module.End ℂ A} {br : LambdaBracket A}
    (hR : HasSesquilinearRight T br) (a b c : A) :
    jacobiMiddle br a b (T c) = jacobiTranslation T (jacobiMiddle br a b c) := by
  simp only [← jacobiMiddleLinear_apply, jacobiMiddleLinear, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [hR, map_add, mapCoefficients_eq_mapRange, expand_mapRange, expand_shift]
  simp only [jacobiTranslation, LinearMap.add_apply, add_assoc]

/-- Translation propagates Jacobi in its last argument; this uses only right
sesquilinearity, not Jacobi itself. -/
theorem jacobiator_translation {T : Module.End ℂ A} {br : LambdaBracket A}
    (hR : HasSesquilinearRight T br) (s : ℂ) (a b c : A) :
    jacobiator br s a b (T c) = jacobiTranslation T (jacobiator br s a b c) := by
  simp only [jacobiator, LinearMap.sub_apply, LinearMap.smul_apply,
    jacobiLeftLinear_apply, jacobiMiddleLinear_apply, jacobiRightLinear_apply,
    jacobiLeft_translation hR, jacobiMiddle_translation hR, jacobiRight_translation hR,
    map_sub, map_smul]

end KhanSL2.LambdaBracket
