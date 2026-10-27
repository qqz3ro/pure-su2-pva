module

public import KhanSL2.Factorization.KunnethGradedTotal

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct DirectSum
open CategoryTheory
namespace KhanSL2.Factorization.GradedTensorTotal

variable (A B : ℕ → ModuleCat.{0} ℂ)

/-- The unchanged degree-p tensor summands, indexed by the first degree. -/
abbrev FiniteTerm (n : ℕ) := ⨁ i : Fin (n+1), A i.val ⊗[ℂ] B (n-i.val)

/-- Insert each actual pair of complementary homological degrees. -/
def finiteToTerm (n : ℕ) : FiniteTerm A B n →ₗ[ℂ] Term A B n :=
  DirectSum.toModule ℂ (Fin (n+1)) _ (fun i =>
    inclusion A B i.val (n-i.val) n (by have hi:=i.isLt; omega))

@[simp] theorem finiteToTerm_of (n : ℕ) (i : Fin (n+1)) (v : A i.val ⊗[ℂ] B (n-i.val)) :
    finiteToTerm A B n (DirectSum.of (fun i : Fin (n+1) => A i.val ⊗[ℂ] B (n-i.val)) i v) =
      inclusion A B i.val (n-i.val) n (by have hi:=i.isLt; omega) v :=
by
  unfold finiteToTerm
  rw [← DirectSum.lof_eq_of ℂ,DirectSum.toModule_lof]

/-- The canonical finite summand belonging to a specified degree pair. -/
def finitePairInclusion (p q n : ℕ) (h : p+q=n) :
    A p ⊗[ℂ] B q →ₗ[ℂ] FiniteTerm A B n := by
  have hp : p<n+1 := by omega
  have hq : q=n-p := by omega
  subst q
  exact DirectSum.lof ℂ (Fin (n+1)) (fun i => A i.val ⊗[ℂ] B (n-i.val)) ⟨p,hp⟩

/-- Split the original categorical degree sum into its finite complementary-degree family. -/
def termToFinite (n : ℕ) : Term A B n →ₗ[ℂ] FiniteTerm A B n :=
  (GradedObject.Monoidal.tensorObjDesc (X₁:=A) (X₂:=B)
    (A:=ModuleCat.of ℂ (FiniteTerm A B n))
    (fun p q h => ModuleCat.ofHom (finitePairInclusion A B p q n h))).hom

@[simp] theorem termToFinite_inclusion (p q n : ℕ) (h : p+q=n) (v : A p⊗[ℂ]B q) :
    termToFinite A B n (inclusion A B p q n h v) = finitePairInclusion A B p q n h v := by
  have he := GradedObject.Monoidal.ι_tensorObjDesc (X₁:=A) (X₂:=B)
    (A:=ModuleCat.of ℂ (FiniteTerm A B n))
    (fun p q h => ModuleCat.ofHom (finitePairInclusion A B p q n h)) p q h
  exact congrArg (fun f => f.hom v) he

theorem termToFinite_finiteToTerm (n : ℕ) (z : FiniteTerm A B n) :
    termToFinite A B n (finiteToTerm A B n z) = z := by
  induction z using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,hx,hy]
  | of i x =>
    rw [finiteToTerm_of,termToFinite_inclusion]
    rfl

theorem finiteToTerm_termToFinite (n : ℕ) (z : Term A B n) :
    finiteToTerm A B n (termToFinite A B n z) = z := by
  have he : ModuleCat.ofHom ((finiteToTerm A B n).comp (termToFinite A B n)) =
      ModuleCat.ofHom (LinearMap.id : Module.End ℂ (Term A B n)) := by
    apply GradedObject.Monoidal.tensorObj_ext
    intro p q h
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change finiteToTerm A B n (termToFinite A B n (inclusion A B p q n h v)) =
      inclusion A B p q n h v
    rw [termToFinite_inclusion]
    have hq : q=n-p := by omega
    subst q
    exact finiteToTerm_of A B n ⟨p,by omega⟩ v
  exact congrArg (fun f => f.hom z) he

/-- The categorical tensor degree sum is precisely the finite direct sum of the original pairs. -/
def finiteTermEquiv (n : ℕ) : FiniteTerm A B n ≃ₗ[ℂ] Term A B n where
  toLinearMap := finiteToTerm A B n
  invFun := termToFinite A B n
  left_inv := termToFinite_finiteToTerm A B n
  right_inv := finiteToTerm_termToFinite A B n

end KhanSL2.Factorization.GradedTensorTotal
