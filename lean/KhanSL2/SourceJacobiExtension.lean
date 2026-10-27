module

public import KhanSL2.PVA
public import KhanSL2.SourceGeneration
public import KhanSL2.SourceSupercomm
public import KhanSL2.LambdaPolynomialLemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.Module

@[expose] public section

/-! Linear extension infrastructure for the super Jacobi identity. -/

noncomputable section

open scoped BigOperators

namespace KhanSL2

theorem koszulSign_comm (d e : Degree) : koszulSign d e = koszulSign e d := by
  simp only [koszulSign, mul_comm]

@[simp] theorem koszulSign_mul_self (d e : Degree) :
    koszulSign d e * koszulSign d e = 1 := by
  unfold koszulSign
  split <;> norm_num

theorem koszulSign_bracket_left (d e f : Degree) (n : ℕ) :
    koszulSign (d.bracket e n) f = koszulSign d f * koszulSign e f := by
  rw [← koszulSign_add_left]
  simp [koszulSign, Degree.bracket, sub_mul, Int.sub_emod, Int.mul_emod]

theorem koszulSign_bracket_right (d e f : Degree) (n : ℕ) :
    koszulSign d (e.bracket f n) = koszulSign d e * koszulSign d f := by
  rw [koszulSign_comm, koszulSign_bracket_left]
  rw [koszulSign_comm e d, koszulSign_comm f d]

end KhanSL2

namespace KhanSL2.LambdaBracket

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

/-- Place a polynomial in a fixed column of a polynomial in two variables. -/
def column (j : ℕ) : LambdaPolynomial A →ₗ[ℂ] TwoLambdaPolynomial A :=
  Finsupp.lsum ℂ fun i => Finsupp.lsingle (i, j)

/-- Place a polynomial in a fixed row of a polynomial in two variables. -/
def row (i : ℕ) : LambdaPolynomial A →ₗ[ℂ] TwoLambdaPolynomial A :=
  Finsupp.lsum ℂ fun j => Finsupp.lsingle (i, j)

@[simp] theorem column_single (i j : ℕ) (a : A) :
    column j (Finsupp.single i a) = Finsupp.single (i, j) a := by
  change (Finsupp.single i a).sum (fun k b => Finsupp.single (k, j) b) = _
  exact Finsupp.sum_single_index (by simp)

@[simp] theorem row_single (i j : ℕ) (a : A) :
    row i (Finsupp.single j a) = Finsupp.single (i, j) a := by
  change (Finsupp.single j a).sum (fun k b => Finsupp.single (i, k) b) = _
  exact Finsupp.sum_single_index (by simp)

theorem column_apply (j : ℕ) (p : LambdaPolynomial A) (i k : ℕ) :
    column j p (i, k) = if j = k then p i else 0 := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, Finsupp.add_apply, hp, hq]
    split <;> simp
  | single n a =>
    rw [column_single]
    by_cases h : j = k
    · subst k
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, h]

theorem row_apply (i : ℕ) (p : LambdaPolynomial A) (j k : ℕ) :
    row i p (j, k) = if i = j then p k else 0 := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
    simp only [map_add, Finsupp.add_apply, hp, hq]
    split <;> simp
  | single n a =>
    rw [row_single]
    by_cases h : i = j
    · subst j
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, h]

/-- Substitute `lambda + mu` and multiply by `lambda^r`. -/
def expand (r : ℕ) : LambdaPolynomial A →ₗ[ℂ] TwoLambdaPolynomial A :=
  Finsupp.lsum ℂ fun s =>
    ∑ i ∈ Finset.range (s + 1),
      (Nat.choose s i : ℂ) • (Finsupp.lsingle (r + i, s - i))

theorem expand_apply (r : ℕ) (p : LambdaPolynomial A) :
    expand r p = p.sum fun s a =>
      ∑ i ∈ Finset.range (s + 1),
        Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • a) := by
  rw [expand, Finsupp.lsum_apply]
  apply Finsupp.sum_congr
  intro s _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lsingle_apply, Finsupp.smul_single]

@[simp] theorem expand_single (r s : ℕ) (a : A) :
    expand r (Finsupp.single s a) =
      ∑ i ∈ Finset.range (s + 1),
        Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • a) := by
  rw [expand_apply, Finsupp.sum_single_index]
  simp

theorem expand_mapRange (r : ℕ) (f : Module.End ℂ A) (p : LambdaPolynomial A) :
    expand r (Finsupp.mapRange.linearMap f p) =
      Finsupp.mapRange.linearMap f (expand r p) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single s a =>
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, expand_single]
    change _ = Finsupp.mapRange.linearMap f _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]

/-- Apply the outer bracket and remember the column of its input coefficient. -/
def leftOnPolynomial (br : LambdaBracket A) (a : A) :
    LambdaPolynomial A →ₗ[ℂ] TwoLambdaPolynomial A :=
  Finsupp.lsum ℂ fun j => (column j).comp (br a)

/-- Apply the outer bracket and remember the row of its input coefficient. -/
def rightOnPolynomial (br : LambdaBracket A) (b : A) :
    LambdaPolynomial A →ₗ[ℂ] TwoLambdaPolynomial A :=
  Finsupp.lsum ℂ fun i => (row i).comp (br b)

theorem leftOnPolynomial_apply (br : LambdaBracket A) (a : A) (p : LambdaPolynomial A) :
    leftOnPolynomial br a p =
      p.sum fun j bc => (br a bc).sum fun i abc => Finsupp.single (i, j) abc := rfl

theorem rightOnPolynomial_apply (br : LambdaBracket A) (b : A) (p : LambdaPolynomial A) :
    rightOnPolynomial br b p =
      p.sum fun i ac => (br b ac).sum fun j bac => Finsupp.single (i, j) bac := rfl

@[simp] theorem leftOnPolynomial_single (br : LambdaBracket A) (a c : A) (j : ℕ) :
    leftOnPolynomial br a (Finsupp.single j c) = column j (br a c) := by
  change (Finsupp.single j c).sum (fun k b => column k (br a b)) = _
  exact Finsupp.sum_single_index (by simp)

@[simp] theorem rightOnPolynomial_single (br : LambdaBracket A) (b c : A) (i : ℕ) :
    rightOnPolynomial br b (Finsupp.single i c) = row i (br b c) := by
  change (Finsupp.single i c).sum (fun k a => row k (br b a)) = _
  exact Finsupp.sum_single_index (by simp)

theorem leftOnPolynomial_coeff (br : LambdaBracket A) (a : A)
    (p : LambdaPolynomial A) (i j : ℕ) :
    leftOnPolynomial br a p (i, j) = br a (p j) i := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single k c =>
    rw [leftOnPolynomial_single, column_apply]
    by_cases h : k = j
    · subst k; simp
    · simp [Finsupp.single_apply, h]

theorem rightOnPolynomial_coeff (br : LambdaBracket A) (b : A)
    (p : LambdaPolynomial A) (i j : ℕ) :
    rightOnPolynomial br b p (i, j) = br b (p i) j := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single k c =>
    rw [rightOnPolynomial_single, row_apply]
    by_cases h : k = i
    · subst k; simp
    · simp [Finsupp.single_apply, h]

/-- The left Jacobi term, bundled as a linear map in its last argument. -/
def jacobiLeftLinear (br : LambdaBracket A) (a b : A) :
    A →ₗ[ℂ] TwoLambdaPolynomial A :=
  (leftOnPolynomial br a).comp (br b)

/-- The right Jacobi term, bundled as a linear map in its last argument. -/
def jacobiRightLinear (br : LambdaBracket A) (a b : A) :
    A →ₗ[ℂ] TwoLambdaPolynomial A :=
  (rightOnPolynomial br b).comp (br a)

/-- The middle Jacobi term, bundled as a linear map in its last argument. -/
def jacobiMiddleLinear (br : LambdaBracket A) (a b : A) :
    A →ₗ[ℂ] TwoLambdaPolynomial A :=
  (br a b).sum fun r ab => (expand r).comp (br ab)

theorem jacobiLeftLinear_apply (br : LambdaBracket A) (a b c : A) :
    jacobiLeftLinear br a b c = jacobiLeft br a b c := rfl

theorem jacobiRightLinear_apply (br : LambdaBracket A) (a b c : A) :
    jacobiRightLinear br a b c = jacobiRight br a b c := rfl

theorem jacobiMiddleLinear_apply (br : LambdaBracket A) (a b c : A) :
    jacobiMiddleLinear br a b c = jacobiMiddle br a b c := by
  simp only [jacobiMiddleLinear, Finsupp.sum, LinearMap.sum_apply, LinearMap.comp_apply,
    expand_apply, jacobiMiddle]

theorem jacobiLeft_coeff (br : LambdaBracket A) (a b c : A) (i j : ℕ) :
    jacobiLeft br a b c (i, j) = br a (br b c j) i :=
  leftOnPolynomial_coeff br a (br b c) i j

theorem jacobiRight_coeff (br : LambdaBracket A) (a b c : A) (i j : ℕ) :
    jacobiRight br a b c (i, j) = br b (br a c i) j :=
  rightOnPolynomial_coeff br b (br a c) i j

/-- Applying a coefficientwise operation commutes with the substitution
in the middle Jacobi term. This is the finite-polynomial distributivity
needed for the derivation rule of the Jacobiator. -/
theorem jacobiMiddle_linear_combination
    (br : LambdaBracket A) (a b u v w : A) (f g : Module.End ℂ A) (s : ℂ)
    (h : ∀ r : ℕ,
      br (br a b r) w =
        Finsupp.mapRange.linearMap f (br (br a b r) u) +
          s • Finsupp.mapRange.linearMap g (br (br a b r) v)) :
    jacobiMiddle br a b w =
      Finsupp.mapRange.linearMap f (jacobiMiddle br a b u) +
        s • Finsupp.mapRange.linearMap g (jacobiMiddle br a b v) := by
  simp only [← jacobiMiddleLinear_apply, jacobiMiddleLinear, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.comp_apply, map_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [h, map_add, map_smul, expand_mapRange, expand_mapRange]

@[simp] theorem jacobiLeft_zero (br : LambdaBracket A) (a b : A) :
    jacobiLeft br a b 0 = 0 :=
  (jacobiLeftLinear br a b).map_zero

@[simp] theorem jacobiRight_zero (br : LambdaBracket A) (a b : A) :
    jacobiRight br a b 0 = 0 :=
  (jacobiRightLinear br a b).map_zero

@[simp] theorem jacobiMiddle_zero (br : LambdaBracket A) (a b : A) :
    jacobiMiddle br a b 0 = 0 := by
  rw [← jacobiMiddleLinear_apply]
  exact (jacobiMiddleLinear br a b).map_zero

@[simp] theorem jacobiLeft_add (br : LambdaBracket A) (a b c d : A) :
    jacobiLeft br a b (c + d) = jacobiLeft br a b c + jacobiLeft br a b d :=
  (jacobiLeftLinear br a b).map_add c d

@[simp] theorem jacobiRight_add (br : LambdaBracket A) (a b c d : A) :
    jacobiRight br a b (c + d) = jacobiRight br a b c + jacobiRight br a b d :=
  (jacobiRightLinear br a b).map_add c d

@[simp] theorem jacobiMiddle_add (br : LambdaBracket A) (a b c d : A) :
    jacobiMiddle br a b (c + d) = jacobiMiddle br a b c + jacobiMiddle br a b d := by
  simp only [← jacobiMiddleLinear_apply, map_add]

@[simp] theorem jacobiLeft_smul (br : LambdaBracket A) (a b c : A) (r : ℂ) :
    jacobiLeft br a b (r • c) = r • jacobiLeft br a b c :=
  (jacobiLeftLinear br a b).map_smul r c

@[simp] theorem jacobiRight_smul (br : LambdaBracket A) (a b c : A) (r : ℂ) :
    jacobiRight br a b (r • c) = r • jacobiRight br a b c :=
  (jacobiRightLinear br a b).map_smul r c

@[simp] theorem jacobiMiddle_smul (br : LambdaBracket A) (a b c : A) (r : ℂ) :
    jacobiMiddle br a b (r • c) = r • jacobiMiddle br a b c := by
  simp only [← jacobiMiddleLinear_apply, map_smul]

/-- The signed Jacobiator is a genuine linear map in its last argument. -/
def jacobiator (br : LambdaBracket A) (s : ℂ) (a b : A) :
    A →ₗ[ℂ] TwoLambdaPolynomial A :=
  jacobiLeftLinear br a b - jacobiMiddleLinear br a b - s • jacobiRightLinear br a b

theorem jacobiator_eq_zero_iff (br : LambdaBracket A) (s : ℂ) (a b c : A) :
    jacobiator br s a b c = 0 ↔
      jacobiLeft br a b c = jacobiMiddle br a b c + s • jacobiRight br a b c := by
  simp only [jacobiator, LinearMap.sub_apply, LinearMap.smul_apply,
    jacobiLeftLinear_apply, jacobiMiddleLinear_apply, jacobiRightLinear_apply]
  rw [sub_sub, sub_eq_zero]

/-- Only the Leibniz law is needed for the product propagation lemmas below. -/
def HasSuperLeibniz (D : DifferentialData A) (br : LambdaBracket A) : Prop :=
  ∀ d e a b c, a ∈ D.piece d → b ∈ D.piece e →
    br a (D.mul b c) =
      (br a b).mulRight D c + koszulSign d e • (br a c).mulLeft D b

/-- Only homogeneity of bracket coefficients is needed in addition. -/
def HasBracketDegree (D : DifferentialData A) (br : LambdaBracket A) : Prop :=
  ∀ d e a b n, a ∈ D.piece d → b ∈ D.piece e →
    br a b n ∈ D.piece (d.bracket e n)

theorem superLeibniz_coeff {D : DifferentialData A} {br : LambdaBracket A}
    (hL : HasSuperLeibniz D br) {d e : Degree} {a b : A}
    (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (c : A) (n : ℕ) :
    br a (D.mul b c) n =
      D.mul (br a b n) c + koszulSign d e • D.mul b (br a c n) := by
  have h := congrArg (fun p : LambdaPolynomial A => p n) (hL d e a b c ha hb)
  simpa only [Finsupp.add_apply, Finsupp.smul_apply, LambdaPolynomial.mulRight_apply,
    LambdaPolynomial.mulLeft_apply] using h

theorem mulRight_eq_mapRange (D : DifferentialData A) (p : LambdaPolynomial A) (a : A) :
    p.mulRight D a = Finsupp.mapRange.linearMap (D.mul.flip a) p := by
  ext n
  simp [LambdaPolynomial.mulRight_apply]

theorem mulLeft_eq_mapRange (D : DifferentialData A) (a : A) (p : LambdaPolynomial A) :
    p.mulLeft D a = Finsupp.mapRange.linearMap (D.mul a) p := by
  ext n
  simp [LambdaPolynomial.mulLeft_apply]

theorem jacobiMiddle_mul {D : DifferentialData A} {br : LambdaBracket A}
    (hL : HasSuperLeibniz D br) (hdeg : HasBracketDegree D br)
    {d e f : Degree} {a b u : A}
    (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (hu : u ∈ D.piece f) (v : A) :
    jacobiMiddle br a b (D.mul u v) =
      Finsupp.mapRange.linearMap (D.mul.flip v) (jacobiMiddle br a b u) +
        (koszulSign d f * koszulSign e f) •
          Finsupp.mapRange.linearMap (D.mul u) (jacobiMiddle br a b v) := by
  apply jacobiMiddle_linear_combination
  intro r
  rw [hL _ _ _ _ _ (hdeg _ _ _ _ _ ha hb) hu, koszulSign_bracket_left,
    mulRight_eq_mapRange, mulLeft_eq_mapRange]

theorem jacobiLeft_mul_coeff {D : DifferentialData A} {br : LambdaBracket A}
    (hL : HasSuperLeibniz D br) (hdeg : HasBracketDegree D br)
    {d e f : Degree} {a b u : A}
    (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (hu : u ∈ D.piece f)
    (v : A) (i j : ℕ) :
    jacobiLeft br a b (D.mul u v) (i, j) =
      D.mul (jacobiLeft br a b u (i, j)) v +
      (koszulSign d e * koszulSign d f) • D.mul (br b u j) (br a v i) +
      koszulSign e f • D.mul (br a u i) (br b v j) +
      (koszulSign d f * koszulSign e f) •
        D.mul u (jacobiLeft br a b v (i, j)) := by
  rw [jacobiLeft_coeff, superLeibniz_coeff hL hb hu]
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply]
  rw [superLeibniz_coeff hL ha (hdeg _ _ _ _ _ hb hu),
    superLeibniz_coeff hL ha hu, koszulSign_bracket_right]
  simp only [jacobiLeft_coeff]
  module

theorem jacobiRight_mul_coeff {D : DifferentialData A} {br : LambdaBracket A}
    (hL : HasSuperLeibniz D br) (hdeg : HasBracketDegree D br)
    {d e f : Degree} {a b u : A}
    (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (hu : u ∈ D.piece f)
    (v : A) (i j : ℕ) :
    jacobiRight br a b (D.mul u v) (i, j) =
      D.mul (jacobiRight br a b u (i, j)) v +
      (koszulSign e d * koszulSign e f) • D.mul (br a u i) (br b v j) +
      koszulSign d f • D.mul (br b u j) (br a v i) +
      (koszulSign d f * koszulSign e f) •
        D.mul u (jacobiRight br a b v (i, j)) := by
  have h := jacobiLeft_mul_coeff hL hdeg hb ha hu v j i
  simpa only [jacobiLeft_coeff, jacobiRight_coeff, mul_comm (koszulSign e f)] using h

/-- The Jacobiator is a superderivation in its third argument.
This follows from Leibniz and homogeneity alone, without assuming Jacobi. -/
theorem jacobiator_mul {D : DifferentialData A} {br : LambdaBracket A}
    (hL : HasSuperLeibniz D br) (hdeg : HasBracketDegree D br)
    {d e f : Degree} {a b u : A}
    (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (hu : u ∈ D.piece f) (v : A) :
    jacobiator br (koszulSign d e) a b (D.mul u v) =
      Finsupp.mapRange.linearMap (D.mul.flip v)
        (jacobiator br (koszulSign d e) a b u) +
        (koszulSign d f * koszulSign e f) •
          Finsupp.mapRange.linearMap (D.mul u)
            (jacobiator br (koszulSign d e) a b v) := by
  ext ⟨i, j⟩
  simp only [jacobiator, LinearMap.sub_apply, LinearMap.smul_apply,
    jacobiLeftLinear_apply, jacobiMiddleLinear_apply, jacobiRightLinear_apply,
    jacobiMiddle_mul hL hdeg ha hb hu, Finsupp.sub_apply, Finsupp.add_apply,
    Finsupp.smul_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply,
    LinearMap.flip_apply]
  rw [jacobiLeft_mul_coeff hL hdeg ha hb hu,
    jacobiRight_mul_coeff hL hdeg ha hb hu, koszulSign_comm e d]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  have hsign := koszulSign_mul_self d e
  match_scalars <;> ring_nf
  simp [pow_two, hsign]

end KhanSL2.LambdaBracket
