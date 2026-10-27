module

public import KhanSL2.Factorization.KunnethField
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Forgetting total degree in a categorical graded tensor is exactly the
ordinary tensor product of the two algebraic direct sums. -/
noncomputable section
open scoped DirectSum TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization.GradedTensorTotal

variable (A B : ℕ → ModuleCat.{0} ℂ)

abbrev Term (n : ℕ) : Type := ↥(GradedObject.Monoidal.tensorObj A B n)
abbrev PairTerm (pq : ℕ × ℕ) := A pq.1 ⊗[ℂ] B pq.2
abbrev inclusion (p q n : ℕ) (h : p+q=n) : PairTerm A B (p,q) →ₗ[ℂ] Term A B n :=
  (GradedObject.Monoidal.ιTensorObj A B p q n h).hom

/-- Regroup each pair of degrees by their sum. -/
def regroup : (⨁ pq, PairTerm A B pq) →ₗ[ℂ] (⨁ n, Term A B n) :=
  DirectSum.toModule ℂ (ℕ × ℕ) _ (fun pq =>
    (DirectSum.lof ℂ ℕ (Term A B) (pq.1+pq.2)).comp
      (inclusion A B pq.1 pq.2 (pq.1+pq.2) rfl))

@[simp] theorem regroup_of (p q : ℕ) (v : PairTerm A B (p,q)) :
    regroup A B (DirectSum.of (PairTerm A B) (p,q) v) =
      DirectSum.of (Term A B) (p+q) (inclusion A B p q (p+q) rfl v) :=
by
  unfold regroup
  rw [← DirectSum.lof_eq_of ℂ,DirectSum.toModule_lof]
  rfl

def ungroupDegree (n : ℕ) : Term A B n →ₗ[ℂ] (⨁ pq, PairTerm A B pq) :=
  (GradedObject.Monoidal.tensorObjDesc (X₁ := A) (X₂ := B)
    (A := ModuleCat.of ℂ (⨁ pq, PairTerm A B pq))
    (fun p q (_ : p+q=n) => ModuleCat.ofHom
      (DirectSum.lof ℂ (ℕ × ℕ) (PairTerm A B) (p,q)))).hom

@[simp] theorem ungroupDegree_inclusion (p q n : ℕ) (h : p+q=n)
    (v : PairTerm A B (p,q)) :
    ungroupDegree A B n (inclusion A B p q n h v) =
      DirectSum.of (PairTerm A B) (p,q) v := by
  have he := GradedObject.Monoidal.ι_tensorObjDesc (X₁ := A) (X₂ := B)
    (A := ModuleCat.of ℂ (⨁ pq, PairTerm A B pq))
    (fun p q (_ : p+q=n) => ModuleCat.ofHom
      (DirectSum.lof ℂ (ℕ × ℕ) (PairTerm A B) (p,q))) p q h
  exact congrArg (fun f => f.hom v) he

/-- Retain each pair of degrees in the categorical summand. -/
def ungroup : (⨁ n, Term A B n) →ₗ[ℂ] (⨁ pq, PairTerm A B pq) :=
  DirectSum.toModule ℂ ℕ _ (ungroupDegree A B)

@[simp] theorem ungroup_of (n : ℕ) (v : Term A B n) :
    ungroup A B (DirectSum.of (Term A B) n v) = ungroupDegree A B n v :=
  DirectSum.toModule_lof ℂ (φ := ungroupDegree A B) n v

theorem ungroup_regroup (u : ⨁ pq, PairTerm A B pq) :
    ungroup A B (regroup A B u) = u := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | of pq u =>
    rcases pq with ⟨p,q⟩
    rw [regroup_of,ungroup_of,ungroupDegree_inclusion]

theorem regroup_ungroupDegree (n : ℕ) (u : Term A B n) :
    regroup A B (ungroupDegree A B n u) = DirectSum.of (Term A B) n u := by
  have he : ModuleCat.ofHom ((regroup A B).comp (ungroupDegree A B n)) =
      ModuleCat.ofHom (DirectSum.lof ℂ ℕ (Term A B) n) := by
    apply GradedObject.Monoidal.tensorObj_ext
    intro p q hpq
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change regroup A B (ungroupDegree A B n (inclusion A B p q n hpq v)) =
      DirectSum.of (Term A B) n (inclusion A B p q n hpq v)
    rw [ungroupDegree_inclusion,regroup_of]
    subst n
    rfl
  exact congrArg (fun f => f.hom u) he

theorem regroup_ungroup (u : ⨁ n, Term A B n) :
    regroup A B (ungroup A B u) = u := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | of n u => rw [ungroup_of,regroup_ungroupDegree]

/-- Regrouping the finite algebraic sum by total degree is an actual equivalence. -/
def regroupEquiv : (⨁ pq, PairTerm A B pq) ≃ₗ[ℂ] (⨁ n, Term A B n) where
  toLinearMap := regroup A B
  invFun := ungroup A B
  left_inv := ungroup_regroup A B
  right_inv := regroup_ungroup A B

/-- The canonical tensor of two sums, with exactly the original inclusion on pure tensors. -/
def tensorEquiv : ((⨁ p, A p) ⊗[ℂ] (⨁ q, B q)) ≃ₗ[ℂ] (⨁ n, Term A B n) :=
  (TensorProduct.directSum ℂ ℂ (fun p => A p) (fun q => B q)).trans (regroupEquiv A B)

@[simp] theorem tensorEquiv_of_tmul (p q : ℕ) (u : A p) (v : B q) :
    tensorEquiv A B (DirectSum.of (fun p => A p) p u ⊗ₜ[ℂ] DirectSum.of (fun q => B q) q v) =
      DirectSum.of (Term A B) (p+q) (inclusion A B p q (p+q) rfl (u ⊗ₜ[ℂ] v)) := by
  rw [tensorEquiv,LinearEquiv.trans_apply,← DirectSum.lof_eq_of ℂ,
    ← DirectSum.lof_eq_of ℂ,TensorProduct.directSum_lof_tmul_lof]
  exact regroup_of A B p q (u ⊗ₜ[ℂ] v)

end KhanSL2.Factorization.GradedTensorTotal
