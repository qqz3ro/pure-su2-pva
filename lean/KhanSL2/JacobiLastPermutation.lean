module

public import KhanSL2.JacobiPermutation
public import KhanSL2.LambdaPolynomialSkew

@[expose] public section

/-! The transposition of the last two arguments of the super Jacobiator. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2.LambdaBracket

variable {A B : Type*} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B]

def nestVariables : TwoLambdaPolynomial A →ₗ[ℂ] LambdaPolynomial (LambdaPolynomial A) :=
  Finsupp.lsum ℂ fun ij => (Finsupp.lsingle ij.2).comp (Finsupp.lsingle ij.1)

def unnestVariables : LambdaPolynomial (LambdaPolynomial A) →ₗ[ℂ] TwoLambdaPolynomial A :=
  Finsupp.lsum ℂ fun j => column j

@[simp] theorem nestVariables_single (i j : ℕ) (a : A) :
    nestVariables (Finsupp.single (i, j) a) = Finsupp.single j (Finsupp.single i a) := by
  change (Finsupp.single (i, j) a).sum
    (fun ij b => Finsupp.single ij.2 (Finsupp.single ij.1 b)) = _
  exact Finsupp.sum_single_index (by simp)

@[simp] theorem unnestVariables_single (j : ℕ) (p : LambdaPolynomial A) :
    unnestVariables (Finsupp.single j p) = column j p := by
  change (Finsupp.single j p).sum (fun j p => column j p) = _
  exact Finsupp.sum_single_index (by simp)

@[simp] theorem nestVariables_column (j : ℕ) (p : LambdaPolynomial A) :
    nestVariables (column j p) = Finsupp.single j p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, Finsupp.single_add]
  | single i a => simp

@[simp] theorem nestVariables_unnest (p : LambdaPolynomial (LambdaPolynomial A)) :
    nestVariables (unnestVariables p) = p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single j p => simp

@[simp] theorem unnestVariables_nest (p : TwoLambdaPolynomial A) :
    unnestVariables (nestVariables p) = p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single ij a => rcases ij with ⟨i, j⟩; simp

theorem nestVariables_leftOnPolynomial (br : LambdaBracket A) (a : A)
    (p : LambdaPolynomial A) :
    nestVariables (leftOnPolynomial br a p) = Finsupp.mapRange.linearMap (br a) p := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single j b => simp

theorem mapRange_skew_natural (T : Module.End ℂ A) (U : Module.End ℂ B)
    (f : A →ₗ[ℂ] B) (hf : ∀ a, f (T a) = U (f a)) (p : LambdaPolynomial A) :
    Finsupp.mapRange.linearMap f (p.minusVariableMinusTranslation T) =
      LambdaPolynomial.minusVariableMinusTranslation U (Finsupp.mapRange.linearMap f p) := by
  have hp : ∀ n a, f ((T ^ n) a) = (U ^ n) (f a) := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      simp only [pow_succ', Module.End.mul_apply, hf, ih]
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [LambdaPolynomial.skew_add, map_add, hp, hq]
  | single n a =>
    have hs : Finsupp.mapRange.linearMap f (Finsupp.single n a) =
        Finsupp.single n (f a) := by simp
    rw [hs, LambdaPolynomial.skew_single, LambdaPolynomial.skew_single, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp [hp]

/-- Substitute `mu` by `-lambda-mu-partial`, retaining `lambda`.
The nested-coefficient construction inherits involutivity from ordinary skew
substitution. -/
def lastSwap (T : Module.End ℂ A) : Module.End ℂ (TwoLambdaPolynomial A) :=
  unnestVariables.comp
    ((LambdaPolynomial.skewLinear (LambdaPolynomial.rightTranslation T)).comp nestVariables)

theorem lastSwap_apply (T : Module.End ℂ A) (p : TwoLambdaPolynomial A) :
    lastSwap T p = unnestVariables
      ((nestVariables p).minusVariableMinusTranslation (LambdaPolynomial.rightTranslation T)) :=
  congrArg unnestVariables (LambdaPolynomial.skewLinear_apply _ _)

@[simp] theorem lastSwap_lastSwap (T : Module.End ℂ A) (p : TwoLambdaPolynomial A) :
    lastSwap T (lastSwap T p) = p := by
  simp only [lastSwap_apply, nestVariables_unnest, LambdaPolynomial.skew_involutive,
    unnestVariables_nest]

theorem lastSwap_column_zero (T : Module.End ℂ A) (p : LambdaPolynomial A) :
    lastSwap T (column 0 p) = column 0 p := by
  simp only [lastSwap_apply, nestVariables_column, LambdaPolynomial.skew_single]
  simp

theorem leftOnPolynomial_skew {T : Module.End ℂ A} {br : LambdaBracket A}
    (hR : HasSesquilinearRight T br) (a : A) (p : LambdaPolynomial A) :
    leftOnPolynomial br a (p.minusVariableMinusTranslation T) =
      lastSwap T (leftOnPolynomial br a p) := by
  have h := mapRange_skew_natural T (LambdaPolynomial.rightTranslation T)
    (br a) (fun b => hR a b) p
  apply_fun unnestVariables at h
  simpa only [← nestVariables_leftOnPolynomial, unnestVariables_nest,
    lastSwap_apply] using h

theorem nestVariables_muShift (p : TwoLambdaPolynomial A) :
    nestVariables (muShift p) = (nestVariables p).shift := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, LambdaPolynomial.shift_add]
  | single ij a => rcases ij with ⟨i, j⟩; simp

theorem unnestVariables_shift (p : LambdaPolynomial (LambdaPolynomial A)) :
    unnestVariables p.shift = muShift (unnestVariables p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [LambdaPolynomial.shift_add, map_add, hp, hq]
  | single j p =>
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq =>
      simp only [Finsupp.single_add, LambdaPolynomial.shift_add, map_add, hp, hq]
    | single i a => simp

theorem unnestVariables_coefficients_rightTranslation (T : Module.End ℂ A)
    (p : LambdaPolynomial (LambdaPolynomial A)) :
    unnestVariables (p.mapCoefficients (LambdaPolynomial.rightTranslation T)) =
      Finsupp.mapRange.linearMap T (unnestVariables p) +
        lambdaShift (unnestVariables p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [LambdaPolynomial.mapCoefficients_add, map_add, hp, hq]
    abel
  | single j p =>
    induction p using Finsupp.induction_linear with
    | zero => simp
    | add p q hp hq =>
      simp only [Finsupp.single_add, LambdaPolynomial.mapCoefficients_add, map_add, hp, hq]
      abel
    | single i a =>
      simp [LambdaPolynomial.rightTranslation_apply]

theorem lastSwap_muShift (T : Module.End ℂ A) (p : TwoLambdaPolynomial A) :
    lastSwap T (muShift p) = -jacobiTranslation T (lastSwap T p) := by
  rw [lastSwap_apply, nestVariables_muShift, LambdaPolynomial.skew_shift, map_sub,
    map_neg, unnestVariables_shift, unnestVariables_coefficients_rightTranslation]
  simp only [lastSwap_apply, jacobiTranslation, LinearMap.add_apply]
  abel

@[simp] theorem lastSwap_single_zero (T : Module.End ℂ A) (i : ℕ) (a : A) :
    lastSwap T (Finsupp.single (i, 0) a) = Finsupp.single (i, 0) a := by
  simpa only [column_single] using lastSwap_column_zero T (Finsupp.single i a)

theorem expand_skew_lastSwap_row (T : Module.End ℂ A) (r : ℕ) (p : LambdaPolynomial A) :
    expand r (p.minusVariableMinusTranslation T) = lastSwap T (row r p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [LambdaPolynomial.skew_add, map_add, hp, hq]
  | single n a =>
    induction n with
    | zero => simp [LambdaPolynomial.skew_single, expand_single]
    | succ n ih =>
      rw [LambdaPolynomial.skew_single_succ, map_sub, map_neg,
        expand_shift, mapCoefficients_eq_mapRange, expand_mapRange, ih]
      have hrow : row r (Finsupp.single (n + 1) a) =
          muShift (row r (Finsupp.single n a)) := by simp
      rw [hrow, lastSwap_muShift]
      simp only [jacobiTranslation, LinearMap.add_apply]
      abel

theorem jacobiLeft_lastSwap {D : DifferentialData A} {br : LambdaBracket A}
    (hR : HasSesquilinearRight D.translation br) (hsk : HasSuperSkew D br)
    {e f : Degree} {b c : A} (hb : b ∈ D.piece e) (hc : c ∈ D.piece f) (a : A) :
    jacobiLeft br a b c =
      (-koszulSign e f) • lastSwap D.translation (jacobiLeft br a c b) := by
  change leftOnPolynomial br a (br b c) =
    (-koszulSign e f) • lastSwap D.translation (leftOnPolynomial br a (br c b))
  rw [hsk e f b c hb hc, map_smul, leftOnPolynomial_skew hR]

theorem jacobiMiddle_lastSwap {D : DifferentialData A} {br : LambdaBracket A}
    (hsk : HasSuperSkew D br) (hdeg : HasBracketDegree D br)
    {d e f : Degree} {a b c : A}
    (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (hc : c ∈ D.piece f) :
    jacobiMiddle br a b c =
      (-(koszulSign d f * koszulSign e f)) •
        lastSwap D.translation (jacobiRight br a c b) := by
  rw [← middleOnPolynomial_br]
  change (br a b).sum (fun r ab => expand r (br ab c)) =
    (-(koszulSign d f * koszulSign e f)) •
      lastSwap D.translation ((br a b).sum (fun r ab => row r (br c ab)))
  simp only [Finsupp.sum, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [hsk _ _ _ _ (hdeg _ _ _ _ _ ha hb) hc, koszulSign_bracket_left, map_smul,
    expand_skew_lastSwap_row]

theorem jacobiRight_lastSwap {D : DifferentialData A} {br : LambdaBracket A}
    (hsk : HasSuperSkew D br) (hdeg : HasBracketDegree D br)
    {d e f : Degree} {a b c : A}
    (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (hc : c ∈ D.piece f) :
    jacobiRight br a b c =
      (-(koszulSign d e * koszulSign e f)) •
        lastSwap D.translation (jacobiMiddle br a c b) := by
  have h := congrArg (fun p : TwoLambdaPolynomial A =>
    (-(koszulSign d e * koszulSign e f)) • lastSwap D.translation p)
    (jacobiMiddle_lastSwap hsk hdeg ha hc hb)
  rw [map_smul, lastSwap_lastSwap, koszulSign_comm f e, smul_smul] at h
  have hsign : (-(koszulSign d e * koszulSign e f)) *
      (-(koszulSign d e * koszulSign e f)) = 1 := by
    rw [neg_mul_neg]
    calc
      _ = (koszulSign d e * koszulSign d e) * (koszulSign e f * koszulSign e f) := by ring
      _ = 1 := by simp
  rw [hsign, one_smul] at h
  exact h.symm

/-- The Jacobiator changes by a Koszul sign and the finite substitution
`mu -> -lambda-mu-partial` on swapping its last two homogeneous arguments. -/
theorem jacobiator_lastSwap {D : DifferentialData A} {br : LambdaBracket A}
    (hR : HasSesquilinearRight D.translation br) (hsk : HasSuperSkew D br)
    (hdeg : HasBracketDegree D br)
    {d e f : Degree} {a b c : A}
    (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (hc : c ∈ D.piece f) :
    jacobiator br (koszulSign d e) a b c =
      (-koszulSign e f) •
        lastSwap D.translation (jacobiator br (koszulSign d f) a c b) := by
  simp only [jacobiator, LinearMap.sub_apply, LinearMap.smul_apply,
    jacobiLeftLinear_apply, jacobiMiddleLinear_apply, jacobiRightLinear_apply,
    map_sub, map_smul]
  rw [jacobiLeft_lastSwap hR hsk hb hc,
    jacobiMiddle_lastSwap hsk hdeg ha hb hc, jacobiRight_lastSwap hsk hdeg ha hb hc]
  match_scalars <;> ring_nf
  simp [pow_two]

end KhanSL2.LambdaBracket
