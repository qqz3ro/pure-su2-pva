module

public import KhanSL2.LambdaPolynomialSkew

@[expose] public section

/-! Polynomial identities for the Wick construction on differential algebras. -/

noncomputable section

namespace KhanSL2.BC.PolynomialCalculus

open LambdaPolynomial

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

def K (D : DifferentialData A) : Module.End ℂ (LambdaPolynomial A) :=
  skewLinear D.translation

def R (D : DifferentialData A) (b : A) : Module.End ℂ (LambdaPolynomial A) :=
  (K D).comp ((mulRightLinear D b).comp (K D))

theorem K_apply (D : DifferentialData A) (p : LambdaPolynomial A) :
    K D p = minusVariableMinusTranslation D.translation p :=
  skewLinear_apply _ _

theorem R_apply (D : DifferentialData A) (b : A) (p : LambdaPolynomial A) :
    R D b p = K D (mulRight D (K D p) b) := rfl

@[simp] theorem K_K (D : DifferentialData A) (p : LambdaPolynomial A) :
    K D (K D p) = p := by
  simp only [K_apply, skew_involutive]

theorem K_rightTranslation (D : DifferentialData A) (p : LambdaPolynomial A) :
    K D (rightTranslation D.translation p) = -shift (K D p) := by
  simp only [rightTranslation_apply, K_apply, skew_add,
    skew_mapCoefficients, skew_shift]
  abel

theorem rightTranslation_K (D : DifferentialData A) (p : LambdaPolynomial A) :
    rightTranslation D.translation (K D p) = K D (-shift p) := by
  have h := congrArg (K D) (K_rightTranslation D (K D p))
  simpa only [K_K] using h

theorem R_translation_commutator (D : DifferentialData A)
    (hT : ∀ a b, D.translation (D.mul a b) =
      D.mul (D.translation a) b + D.mul a (D.translation b))
    (a : A) (p : LambdaPolynomial A) :
    -shift (R D a p) = R D (D.translation a) p + R D a (-shift p) := by
  rw [R_apply, ← K_rightTranslation]
  rw [rightTranslation_mulRight D hT, map_add, rightTranslation_K, add_comm]
  rfl

theorem R_shift (D : DifferentialData A)
    (hT : ∀ a b, D.translation (D.mul a b) =
      D.mul (D.translation a) b + D.mul a (D.translation b))
    (a : A) (p : LambdaPolynomial A) :
    R D a (shift p) = shift (R D a p) + R D (D.translation a) p := by
  have h := congrArg Neg.neg (R_translation_commutator D hT a p)
  simp only [map_neg, neg_neg, neg_add_rev] at h
  rw [h]
  abel

@[simp] theorem R_single_zero (D : DifferentialData A) (a b : A) :
    R D b (Finsupp.single 0 a) = Finsupp.single 0 (D.mul a b) := by
  simp [R_apply, K_apply, skew_single]

theorem R_single_succ (D : DifferentialData A)
    (hT : ∀ a b, D.translation (D.mul a b) =
      D.mul (D.translation a) b + D.mul a (D.translation b))
    (a b : A) (n : ℕ) :
    R D b (Finsupp.single (n + 1) a) =
      shift (R D b (Finsupp.single n a)) +
        R D (D.translation b) (Finsupp.single n a) := by
  rw [← shift_single, R_shift D hT]

theorem shift_mulRight (D : DifferentialData A) (p : LambdaPolynomial A) (b : A) :
    shift (mulRight D p b) = mulRight D (shift p) b := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single n a => simp

theorem K_single_translation (D : DifferentialData A) (b : A) (n : ℕ) :
    K D (Finsupp.single n (D.translation b)) =
      mapCoefficients D.translation (K D (Finsupp.single n b)) := by
  rw [← mapCoefficients_single]
  simp only [K_apply, skew_mapCoefficients]

/-- Move a polynomial coefficient through skew substitution. The hypothesis
states exactly the supercommutation needed for all derivatives of `b`. -/
theorem R_single_swap (D : DifferentialData A)
    (hT : ∀ a b, D.translation (D.mul a b) =
      D.mul (D.translation a) b + D.mul a (D.translation b))
    (a b : A) (sign : ℂ)
    (hcomm : ∀ k : ℕ, D.mul a ((D.translation ^ k) b) =
      sign • D.mul ((D.translation ^ k) b) a) (n : ℕ) :
    R D b (Finsupp.single n a) =
      ((-1 : ℂ) ^ n * sign) • mulRight D (K D (Finsupp.single n b)) a := by
  induction n generalizing b with
  | zero =>
    have h := hcomm 0
    simp only [pow_zero, Module.End.one_apply] at h
    simp [K_apply, skew_single, h]
  | succ n ih =>
    have ht : ∀ k : ℕ, D.mul a ((D.translation ^ k) (D.translation b)) =
        sign • D.mul ((D.translation ^ k) (D.translation b)) a := by
      intro k
      simpa only [pow_succ, Module.End.mul_apply] using hcomm (k + 1)
    rw [R_single_succ D hT, ih b hcomm, ih (D.translation b) ht]
    rw [K_single_translation]
    simp only [shift_smul, shift_mulRight, ← smul_add, ← mulRight_add]
    rw [show shift (K D (Finsupp.single n b)) +
        mapCoefficients D.translation (K D (Finsupp.single n b)) =
        -K D (Finsupp.single (n + 1) b) by
      simp only [K_apply]
      rw [skew_single_succ]
      abel]
    have hn : ∀ p : LambdaPolynomial A, mulRight D (-p) a = -mulRight D p a :=
      fun p => (mulRightLinear D a).map_neg p
    simp [hn, pow_succ, mul_smul, mul_assoc, mul_comm, mul_left_comm]

end KhanSL2.BC.PolynomialCalculus
