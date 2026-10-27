module

public import KhanSL2.SourceJacobiExtension

@[expose] public section

/-! Hamiltonian zero modes are derivations of the exact PVA operations. -/

noncomputable section

namespace KhanSL2

open LambdaPolynomial LambdaBracket

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

namespace LambdaBracket

theorem expand_zero_coeff (r : ℕ) (p : LambdaPolynomial A) (j : ℕ) :
    expand r p (0, j) = if r = 0 then p j else 0 := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]; split <;> simp
  | single s a =>
    rw [expand_single]
    by_cases hr : r = 0
    · subst r
      simp [Finset.sum_apply', Finsupp.single_apply, Prod.mk.injEq,
        Finset.sum_ite_irrel, Nat.zero_lt_succ]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro i _ hi
        simp [hi]
      · intro h
        exact False.elim (h (by simp))
    · simp only [ite_eq_right hr, Finset.sum_apply']
      apply Finset.sum_eq_zero
      intro i _
      have hi : r + i ≠ 0 := by omega
      simp [Finsupp.single_apply, Prod.mk.injEq, hi, hr]

theorem jacobiMiddle_zero_coeff (br : LambdaBracket A) (a b c : A) (n : ℕ) :
    jacobiMiddle br a b c (0, n) = br (br a b 0) c n := by
  simp only [← jacobiMiddleLinear_apply, jacobiMiddleLinear, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.comp_apply, Finset.sum_apply',
    expand_zero_coeff]
  by_cases h : (br a b) 0 = 0
  · simp [h, Finsupp.mem_support_iff]
  · simp [h, Finsupp.mem_support_iff]

def zeroMode (br : LambdaBracket A) (a : A) : Module.End ℂ A where
  toFun b := br a b 0
  map_add' b c := by simp
  map_smul' r b := by simp

@[simp] theorem zeroMode_apply (br : LambdaBracket A) (a b : A) :
    zeroMode br a b = br a b 0 := rfl

theorem zeroMode_translation {D : DifferentialData A} {br : LambdaBracket A}
    (hP : IsPVA D br) (a b : A) :
    zeroMode br a (D.translation b) = D.translation (zeroMode br a b) := by
  have h := congrArg (fun p : LambdaPolynomial A => p 0) (hP.sesquilinear_right a b)
  simpa [mapCoefficients_apply] using h

theorem zeroMode_mul {D : DifferentialData A} {br : LambdaBracket A}
    (hP : IsPVA D br) {d e : Degree} {a b : A}
    (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (c : A) :
    zeroMode br a (D.mul b c) =
      D.mul (zeroMode br a b) c + koszulSign d e • D.mul b (zeroMode br a c) := by
  have h := congrArg (fun p : LambdaPolynomial A => p 0)
    (hP.super_leibniz d e a b c ha hb)
  simpa [mulRight_apply, mulLeft_apply] using h

theorem zeroMode_bracket {D : DifferentialData A} {br : LambdaBracket A}
    (hP : IsPVA D br) {d e : Degree} {a b : A}
    (ha : a ∈ D.piece d) (hb : b ∈ D.piece e) (c : A) (n : ℕ) :
    zeroMode br a (br b c n) =
      br (zeroMode br a b) c n + koszulSign d e • br b (zeroMode br a c) n := by
  have h := congrArg (fun p : TwoLambdaPolynomial A => p (0, n))
    (hP.super_jacobi d e a b c ha hb)
  simpa only [jacobiLeft_coeff, jacobiRight_coeff, jacobiMiddle_zero_coeff,
    Finsupp.add_apply, Finsupp.smul_apply, zeroMode_apply] using h

end LambdaBracket
end KhanSL2
