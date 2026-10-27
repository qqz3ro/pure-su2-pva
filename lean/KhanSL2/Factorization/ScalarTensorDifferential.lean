module

public import KhanSL2.Factorization.ScalarTensorEquivalence
public import TauCeti.Algebra.Homology.Monoidal.Tensor.Differential

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct
open CategoryTheory HomologicalComplex MonoidalCategory
namespace KhanSL2.Factorization.NonnegativeCone

variable {R : Type} [CommRing R]
variable (C D : ChainComplex (ModuleCat R) ℕ)

theorem tensorDifferential_zero_succ (n:ℕ) (u:C.X 0) (v:D.X (n+1)) :
    (HomologicalComplex.tensorObj C D).d (n+1) n (ιTensorObj C D 0 (n+1) (n+1) (by omega) (u⊗ₜ[R]v)) =
      ιTensorObj C D 0 n n (by omega) (u⊗ₜ[R](D.d (n+1) n v)) := by
  have h : ιTensorObj C D 0 (n+1) (n+1) (by omega) ≫ (HomologicalComplex.tensorObj C D).d (n+1) n =
      (C.X 0 ◁ D.d (n+1) n) ≫ ιTensorObj C D 0 n n (by omega) := by
    rw [mapBifunctor.d_eq,Preadditive.comp_add,ChainComplex.ιTensorObj_D₁_zero,
      ChainComplex.ιTensorObj_D₂_succ]
    simp
  exact congrArg (fun f => f.hom (u⊗ₜ[R]v)) h

theorem tensorDifferential_succ_zero (n:ℕ) (u:C.X (n+1)) (v:D.X 0) :
    (HomologicalComplex.tensorObj C D).d (n+1) n (ιTensorObj C D (n+1) 0 (n+1) (by omega) (u⊗ₜ[R]v)) =
      ιTensorObj C D n 0 n (by omega) ((C.d (n+1) n u)⊗ₜ[R]v) := by
  have h : ιTensorObj C D (n+1) 0 (n+1) (by omega) ≫ (HomologicalComplex.tensorObj C D).d (n+1) n =
      (C.d (n+1) n ▷ D.X 0) ≫ ιTensorObj C D n 0 n (by omega) := by
    rw [mapBifunctor.d_eq,Preadditive.comp_add,ChainComplex.ιTensorObj_D₁_succ,
      ChainComplex.ιTensorObj_D₂_zero,add_zero]
  exact congrArg (fun f => f.hom (u⊗ₜ[R]v)) h

theorem tensorDifferential_succ_succ (p q n:ℕ) (h:p+1+(q+1)=n+1)
    (u:C.X (p+1)) (v:D.X (q+1)) :
    (HomologicalComplex.tensorObj C D).d (n+1) n (ιTensorObj C D (p+1) (q+1) (n+1) h (u⊗ₜ[R]v)) =
      ιTensorObj C D p (q+1) n (by omega) ((C.d (p+1) p u)⊗ₜ[R]v) +
        ((-1:ℤ)^(p+1)) • ιTensorObj C D (p+1) q n (by omega) (u⊗ₜ[R](D.d (q+1) q v)) := by
  have hd : ιTensorObj C D (p+1) (q+1) (n+1) h ≫ (HomologicalComplex.tensorObj C D).d (n+1) n =
      (C.d (p+1) p ▷ D.X (q+1)) ≫ ιTensorObj C D p (q+1) n (by omega) +
      ((-1:ℤ)^(p+1)) • ((C.X (p+1) ◁ D.d (q+1) q) ≫ ιTensorObj C D (p+1) q n (by omega)) := by
    rw [mapBifunctor.d_eq,Preadditive.comp_add,ChainComplex.ιTensorObj_D₁_succ,
      ChainComplex.ιTensorObj_D₂_succ]
  exact congrArg (fun f => f.hom (u⊗ₜ[R]v)) hd

end KhanSL2.Factorization.NonnegativeCone



