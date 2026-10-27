module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import KhanSL2.Basic

@[expose] public section

/-!
# Graded even super Poisson vertex algebras

This file defines the full laws, rather than assuming that any of the concrete
objects in the main statement satisfy them. Lambda brackets are ordinary
polynomials with coefficients in a vector space. In particular, the coefficient
of `λ^n` is not divided by `n!`.
-/

noncomputable section

open scoped BigOperators

namespace KhanSL2

def Degree.add (d e : Degree) : Degree :=
  (d.1 + e.1, d.2.1 + e.2.1, d.2.2 + e.2.2)

def Degree.translate (d : Degree) : Degree :=
  (d.1, d.2.1, d.2.2 + 1)

/-- The coefficient of `λ^n` in the bracket has this degree. -/
def Degree.bracket (d e : Degree) (n : ℕ) : Degree :=
  (d.1 + e.1 - 2, d.2.1 + e.2.1 - 1, d.2.2 + e.2.2 - 1 - n)

/-- The Koszul sign depends on total CE degree, not on the `c`-count alone. -/
def koszulSign (d e : Degree) : ℂ :=
  if (d.1 * e.1) % 2 = 0 then 1 else -1

variable (A : Type*) [AddCommGroup A] [Module ℂ A]

/-- Raw operations. Their laws are the separate proposition below. -/
structure DifferentialData where
  one : A
  mul : A →ₗ[ℂ] A →ₗ[ℂ] A
  translation : Module.End ℂ A
  piece : Degree → Submodule ℂ A

/-- Genuine direct-sum grading and all differential superalgebra laws. -/
structure IsGradedDifferentialSuperalgebra (D : DifferentialData A) : Prop where
  grading_internal : DirectSum.IsInternal D.piece
  one_mul : ∀ a, D.mul D.one a = a
  mul_one : ∀ a, D.mul a D.one = a
  mul_assoc : ∀ a b c, D.mul (D.mul a b) c = D.mul a (D.mul b c)
  supercomm : ∀ d e a b, a ∈ D.piece d → b ∈ D.piece e →
    D.mul a b = koszulSign d e • D.mul b a
  one_degree : D.one ∈ D.piece (0, 0, 0)
  mul_degree : ∀ d e a b, a ∈ D.piece d → b ∈ D.piece e →
    D.mul a b ∈ D.piece (d.add e)
  translation_degree : ∀ d a, a ∈ D.piece d →
    D.translation a ∈ D.piece d.translate
  translation_one : D.translation D.one = 0
  translation_mul : ∀ a b,
    D.translation (D.mul a b) =
      D.mul (D.translation a) b + D.mul a (D.translation b)

abbrev LambdaPolynomial := ℕ →₀ A
abbrev TwoLambdaPolynomial := (ℕ × ℕ) →₀ A
abbrev LambdaBracket := A →ₗ[ℂ] A →ₗ[ℂ] LambdaPolynomial A

variable {A}

namespace LambdaPolynomial

/-- Multiplication by the formal variable `λ`. -/
def shift (p : LambdaPolynomial A) : LambdaPolynomial A :=
  p.sum fun n a => Finsupp.single (n + 1) a

/-- Apply an operation to coefficients. Used only for linear operations. -/
def mapCoefficients (f : A →ₗ[ℂ] A) (p : LambdaPolynomial A) :
    LambdaPolynomial A :=
  p.sum fun n a => Finsupp.single n (f a)

/-- Substitute `-λ-∂`, letting every occurrence of `∂` act on the coefficient
to its right. The binomial coefficient is necessary for ordinary polynomials. -/
def minusVariableMinusTranslation (deriv : Module.End ℂ A)
    (p : LambdaPolynomial A) : LambdaPolynomial A :=
  p.sum fun n a =>
    ∑ j ∈ Finset.range (n + 1),
      Finsupp.single j
        (((-1 : ℂ) ^ n * (Nat.choose n j : ℂ)) • ((deriv ^ (n - j)) a))

/-- Coefficientwise right multiplication. -/
def mulRight (D : DifferentialData A) (p : LambdaPolynomial A) (b : A) :
    LambdaPolynomial A :=
  p.sum fun n a => Finsupp.single n (D.mul a b)

/-- Coefficientwise left multiplication. -/
def mulLeft (D : DifferentialData A) (a : A) (p : LambdaPolynomial A) :
    LambdaPolynomial A :=
  p.sum fun n b => Finsupp.single n (D.mul a b)

end LambdaPolynomial

namespace LambdaBracket

/-- `{a_λ {b_μ c}}`, with exponents stored in the order `(λ, μ)`. -/
def jacobiLeft (br : LambdaBracket A) (a b c : A) : TwoLambdaPolynomial A :=
  (br b c).sum fun j bc =>
    (br a bc).sum fun i abc => Finsupp.single (i, j) abc

/-- `{b_μ {a_λ c}}`, in the same `(λ, μ)` coordinate order. -/
def jacobiRight (br : LambdaBracket A) (a b c : A) : TwoLambdaPolynomial A :=
  (br a c).sum fun i ac =>
    (br b ac).sum fun j bac => Finsupp.single (i, j) bac

/-- `{{a_λ b}_{λ+μ} c}`. The factor `λ^r` from the inner bracket stays
outside the substitution of `λ+μ` into the outer bracket. -/
def jacobiMiddle (br : LambdaBracket A) (a b c : A) : TwoLambdaPolynomial A :=
  (br a b).sum fun r ab =>
    (br ab c).sum fun s abc =>
      ∑ i ∈ Finset.range (s + 1),
        Finsupp.single (r + i, s - i) ((Nat.choose s i : ℂ) • abc)

end LambdaBracket

/-- The full even super PVA axioms. Skew symmetry, Jacobi, and Leibniz use
homogeneous arguments wherever a Koszul sign is needed. Bilinearity extends
these laws to arbitrary finite sums of homogeneous elements. -/
structure IsPVA (D : DifferentialData A) (br : LambdaBracket A) : Prop where
  algebra : IsGradedDifferentialSuperalgebra A D
  sesquilinear_left : ∀ a b,
    br (D.translation a) b = -(br a b).shift
  sesquilinear_right : ∀ a b,
    br a (D.translation b) =
      (br a b).mapCoefficients D.translation + (br a b).shift
  super_skew : ∀ d e a b, a ∈ D.piece d → b ∈ D.piece e →
    br a b = (-koszulSign d e) •
      (br b a).minusVariableMinusTranslation D.translation
  super_jacobi : ∀ d e a b c, a ∈ D.piece d → b ∈ D.piece e →
    br.jacobiLeft a b c =
      br.jacobiMiddle a b c + koszulSign d e • br.jacobiRight a b c
  super_leibniz : ∀ d e a b c, a ∈ D.piece d → b ∈ D.piece e →
    br a (D.mul b c) =
      (br a b).mulRight D c + koszulSign d e • (br a c).mulLeft D b
  bracket_degree : ∀ d e a b n, a ∈ D.piece d → b ∈ D.piece e →
    br a b n ∈ D.piece (d.bracket e n)

variable {B : Type*} [AddCommGroup B] [Module ℂ B]

/-- A grading-preserving, unital differential PVA isomorphism. This structure
records the intertwining equations; the PVA laws are stated separately. -/
structure GradedDifferentialPVAEquiv
    (DA : DifferentialData A) (brA : LambdaBracket A)
    (DB : DifferentialData B) (brB : LambdaBracket B) extends A ≃ₗ[ℂ] B where
  map_one : toLinearEquiv DA.one = DB.one
  map_mul : ∀ a b,
    toLinearEquiv (DA.mul a b) = DB.mul (toLinearEquiv a) (toLinearEquiv b)
  map_translation : ∀ a,
    toLinearEquiv (DA.translation a) = DB.translation (toLinearEquiv a)
  map_bracket : ∀ a b n,
    toLinearEquiv (brA a b n) = brB (toLinearEquiv a) (toLinearEquiv b) n
  map_degree : ∀ d a, toLinearEquiv a ∈ DB.piece d ↔ a ∈ DA.piece d

end KhanSL2
