module

public import KhanSL2.Factorization.EvenTensorWords
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The genuine monic coefficient polynomial of an evaluation tensor word.
Distinct support branches give precisely the coprime charts used in factorization. -/
noncomputable section
open Polynomial
namespace KhanSL2.Factorization.EvenTensorWord

/-- Retain each support point with its specified local multiplicity. -/
def polynomial : EvenTensorWord → ℂ[X]
  | leaf a q => (X-C a)^q
  | tensor u v => u.polynomial*v.polynomial

/-- Every prescribed coefficient polynomial is monic, including zero-weight leaves. -/
theorem polynomial_monic (t : EvenTensorWord) : t.polynomial.Monic := by
  induction t with
  | leaf a q => exact (monic_X_sub_C a).pow q
  | tensor u v ihu ihv => exact ihu.mul ihv

/-- Its degree is exactly the total half-highest-weight. -/
theorem polynomial_natDegree (t : EvenTensorWord) : t.polynomial.natDegree = t.weight := by
  induction t with
  | leaf a q => simp [polynomial,weight]
  | tensor u v ihu ihv =>
    change (u.polynomial*v.polynomial).natDegree = u.weight+v.weight
    rw [natDegree_mul (u.polynomial_monic.ne_zero) (v.polynomial_monic.ne_zero),ihu,ihv]

/-- No root of the coefficient polynomial lies outside the specified support. -/
theorem mem_support_of_eval_eq_zero (t : EvenTensorWord) (z : ℂ)
    (hz : t.polynomial.eval z = 0) : z ∈ t.support := by
  induction t with
  | leaf a q =>
    have h : (z-a)^q = 0 := by simpa only [polynomial,eval_pow,eval_sub,eval_X,eval_C] using hz
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero h)
  | tensor u v ihu ihv =>
    have h : u.polynomial.eval z * v.polynomial.eval z = 0 := by
      simpa only [polynomial,eval_mul] using hz
    exact (mul_eq_zero.mp h).elim (fun h => Or.inl (ihu h)) (fun h => Or.inr (ihv h))

/-- The actual factor polynomials are coprime whenever their declared supports are disjoint. -/
theorem polynomial_isCoprime (u v : EvenTensorWord) (h : Disjoint u.support v.support) :
    IsCoprime u.polynomial v.polynomial := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ _ _).mpr
  intro z
  by_cases hu : u.polynomial.eval z = 0
  · right
    intro hv
    apply Set.disjoint_left.mp h (u.mem_support_of_eval_eq_zero z hu)
    apply v.mem_support_of_eval_eq_zero z
    simpa only [aeval_def,Algebra.algebraMap_self,eval₂_id] using hv
  · left
    simpa only [aeval_def,Algebra.algebraMap_self,eval₂_id] using hu

end KhanSL2.Factorization.EvenTensorWord
