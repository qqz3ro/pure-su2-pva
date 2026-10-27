module

public import KhanSL2.JacobiTranslation

@[expose] public section

/-! Permutation and skew substitution for the bivariate Jacobi polynomials. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.LambdaBracket

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

def swapVariables : Module.End ℂ (TwoLambdaPolynomial A) :=
  Finsupp.lsum ℂ fun ij => Finsupp.lsingle (ij.2, ij.1)

@[simp] theorem swapVariables_single (i j : ℕ) (a : A) :
    swapVariables (Finsupp.single (i, j) a) = Finsupp.single (j, i) a := by
  change (Finsupp.single (i, j) a).sum
    (fun ij b => Finsupp.single (ij.2, ij.1) b) = _
  exact Finsupp.sum_single_index (by simp)

@[simp] theorem swapVariables_coeff (p : TwoLambdaPolynomial A) (i j : ℕ) :
    swapVariables p (i, j) = p (j, i) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single ij a =>
    rcases ij with ⟨k, l⟩
    simp [Finsupp.single_apply, and_comm]

@[simp] theorem swapVariables_swap (p : TwoLambdaPolynomial A) :
    swapVariables (swapVariables p) = p := by
  ext ⟨i, j⟩
  simp

theorem swapVariables_lambdaShift (p : TwoLambdaPolynomial A) :
    swapVariables (lambdaShift p) = muShift (swapVariables p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single ij a => rcases ij with ⟨i, j⟩; simp

theorem swapVariables_muShift (p : TwoLambdaPolynomial A) :
    swapVariables (muShift p) = lambdaShift (swapVariables p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single ij a => rcases ij with ⟨i, j⟩; simp

theorem swapVariables_lambdaShift_pow (n : ℕ) (p : TwoLambdaPolynomial A) :
    swapVariables ((lambdaShift ^ n) p) = (muShift ^ n) (swapVariables p) := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', swapVariables_lambdaShift, ih]

theorem swapVariables_shiftSum (p : TwoLambdaPolynomial A) :
    swapVariables ((lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A)) p) =
      (lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A)) (swapVariables p) := by
  simp only [LinearMap.add_apply, map_add, swapVariables_lambdaShift, swapVariables_muShift]
  exact add_comm _ _

theorem swapVariables_shiftSum_pow (n : ℕ) (p : TwoLambdaPolynomial A) :
    swapVariables (((lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A)) ^ n) p) =
      ((lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A)) ^ n)
        (swapVariables p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply]
    rw [swapVariables_shiftSum, ih]

theorem expand_eq_lambdaShift_pow (r : ℕ) (p : LambdaPolynomial A) :
    expand r p = (lambdaShift ^ r) (expand 0 p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single s a =>
    rw [expand_single, expand_single, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [Finsupp.single_smul, add_comm]

theorem swapVariables_expand_zero (p : LambdaPolynomial A) :
    swapVariables (expand 0 p) = expand 0 p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single s a =>
    rw [expand_single_eq_pow, swapVariables_shiftSum_pow, swapVariables_single]

theorem swapVariables_expand (r : ℕ) (p : LambdaPolynomial A) :
    swapVariables (expand r p) = (muShift ^ r) (expand 0 p) := by
  rw [expand_eq_lambdaShift_pow, swapVariables_lambdaShift_pow, swapVariables_expand_zero]

theorem swapVariables_jacobiLeft (br : LambdaBracket A) (a b c : A) :
    swapVariables (jacobiLeft br a b c) = jacobiRight br b a c := by
  ext ⟨i, j⟩
  simp only [swapVariables_coeff, jacobiLeft_coeff, jacobiRight_coeff]

theorem swapVariables_jacobiRight (br : LambdaBracket A) (a b c : A) :
    swapVariables (jacobiRight br a b c) = jacobiLeft br b a c := by
  ext ⟨i, j⟩
  simp only [swapVariables_coeff, jacobiLeft_coeff, jacobiRight_coeff]

def middleOnPolynomial (br : LambdaBracket A) (c : A) :
    LambdaPolynomial A →ₗ[ℂ] TwoLambdaPolynomial A :=
  Finsupp.lsum ℂ fun r => (expand r).comp (br.flip c)

@[simp] theorem middleOnPolynomial_single (br : LambdaBracket A) (c a : A) (r : ℕ) :
    middleOnPolynomial br c (Finsupp.single r a) = expand r (br a c) := by
  change (Finsupp.single r a).sum (fun n b => expand n (br b c)) = _
  exact Finsupp.sum_single_index (by simp)

theorem middleOnPolynomial_br (br : LambdaBracket A) (a b c : A) :
    middleOnPolynomial br c (br a b) = jacobiMiddle br a b c := by
  change (br a b).sum (fun r ab => expand r (br ab c)) = _
  simp only [expand_apply, jacobiMiddle]

def HasSesquilinearLeft (T : Module.End ℂ A) (br : LambdaBracket A) : Prop :=
  ∀ a b, br (T a) b = -(br a b).shift

theorem expandedBracket_translation {T : Module.End ℂ A} {br : LambdaBracket A}
    (hL : HasSesquilinearLeft T br) (a c : A) :
    expand 0 (br (T a) c) =
      (-(lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A)))
        (expand 0 (br a c)) := by
  rw [hL, map_neg, expand_shift, LinearMap.neg_apply]

theorem expandedBracket_translation_pow {T : Module.End ℂ A} {br : LambdaBracket A}
    (hL : HasSesquilinearLeft T br) (a c : A) (n : ℕ) :
    expand 0 (br ((T ^ n) a) c) =
      ((-(lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A))) ^ n)
        (expand 0 (br a c)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, expandedBracket_translation hL,
      ih, pow_succ', Module.End.mul_apply]

theorem expand_translatedBracket {T : Module.End ℂ A} {br : LambdaBracket A}
    (hL : HasSesquilinearLeft T br) (a c : A) (r n : ℕ) :
    expand r (br ((T ^ n) a) c) =
      (lambdaShift ^ r)
        (((-(lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A))) ^ n)
          (expand 0 (br a c))) := by
  rw [expand_eq_lambdaShift_pow, expandedBracket_translation_pow hL]

theorem signed_neg_pow (F : Module.End ℂ A) (n : ℕ) (a : A) :
    (-1 : ℂ) ^ n • ((-F) ^ n) a = (F ^ n) a := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, mul_smul,
      neg_one_smul, smul_neg, neg_neg]
    rw [← map_smul, ih]

theorem shift_difference_binomial (n : ℕ) (p : TwoLambdaPolynomial A) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℂ) •
        (lambdaShift ^ i)
          (((-(lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A))) ^
            (n - i)) p)) = ((-muShift) ^ n) p := by
  have hc :
      Commute (lambdaShift (A := A))
        (-(lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A))) :=
    ((Commute.refl _).add_right shifts_commute).neg_right
  have heq : lambdaShift + -(lambdaShift + muShift : Module.End ℂ (TwoLambdaPolynomial A)) =
      -muShift := by abel
  rw [← heq, hc.add_pow, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul,
    Nat.cast_smul_eq_nsmul]

/-- The inner skew substitution turns the inner `lambda` powers into `mu`
powers after the outer bracket is evaluated at `lambda + mu`. -/
theorem middleOnPolynomial_skew {T : Module.End ℂ A} {br : LambdaBracket A}
    (hL : HasSesquilinearLeft T br) (c : A) (p : LambdaPolynomial A) :
    middleOnPolynomial br c (p.minusVariableMinusTranslation T) =
      swapVariables (middleOnPolynomial br c p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [LambdaPolynomial.skew_add, map_add, hp, hq]
  | single n a =>
    rw [LambdaPolynomial.skew_single, map_sum, middleOnPolynomial_single,
      swapVariables_expand]
    simp only [Finsupp.single_smul, map_smul, LinearMap.smul_apply, middleOnPolynomial_single,
      expand_translatedBracket hL]
    simp only [mul_smul, ← Finset.smul_sum]
    rw [shift_difference_binomial, signed_neg_pow]

def HasSuperSkew (D : DifferentialData A) (br : LambdaBracket A) : Prop :=
  ∀ d e a b, a ∈ D.piece d → b ∈ D.piece e →
    br a b = (-koszulSign d e) •
      (br b a).minusVariableMinusTranslation D.translation

theorem jacobiMiddle_skew {D : DifferentialData A} {br : LambdaBracket A}
    (hL : HasSesquilinearLeft D.translation br) (hsk : HasSuperSkew D br)
    {d e : Degree} {a b : A} (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (c : A) :
    jacobiMiddle br a b c =
      (-koszulSign d e) • swapVariables (jacobiMiddle br b a c) := by
  rw [← middleOnPolynomial_br, hsk d e a b ha hb, map_smul,
    middleOnPolynomial_skew hL, middleOnPolynomial_br]

/-- Swapping the first two arguments changes the Jacobiator by the expected
Koszul sign and exchanges its two formal variables. -/
theorem jacobiator_swap {D : DifferentialData A} {br : LambdaBracket A}
    (hL : HasSesquilinearLeft D.translation br) (hsk : HasSuperSkew D br)
    {d e : Degree} {a b : A} (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (c : A) :
    jacobiator br (koszulSign d e) a b c =
      (-koszulSign d e) • swapVariables (jacobiator br (koszulSign e d) b a c) := by
  simp only [jacobiator, LinearMap.sub_apply, LinearMap.smul_apply,
    jacobiLeftLinear_apply, jacobiMiddleLinear_apply, jacobiRightLinear_apply,
    map_sub, map_smul, swapVariables_jacobiLeft, swapVariables_jacobiRight,
    koszulSign_comm e d]
  rw [jacobiMiddle_skew hL hsk ha hb]
  match_scalars <;> ring_nf
  simp [pow_two]

end KhanSL2.LambdaBracket
