module

public import KhanSL2.Factorization.ScalarTensorDifferential

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization.NonnegativeCone

variable {R : Type} [CommRing R]
variable (A : Type) [CommRing A] [Algebra R A]
variable (C D : ChainComplex (ModuleCat R) ℕ)
attribute [local instance] scalarTensorRestrictModule scalarTensorRestrictTower scalarTensorRestrictComm

/-- The scalar unit commutes with the actual signed tensor boundary. -/
theorem scalarTensorDegreeUnit_differential (n:ℕ) (z:(tensorObj C D).X (n+1)) :
    scalarTensorDegreeUnit A C D n ((tensorObj C D).d (n+1) n z) =
      (scalarTensorComplex A C D).d (n+1) n (scalarTensorDegreeUnit A C D (n+1) z) := by
  have he : ModuleCat.ofHom ((scalarTensorDegreeUnit A C D n).comp
      ((tensorObj C D).d (n+1) n).hom) =
    ModuleCat.ofHom ((((scalarTensorComplex A C D).d (n+1) n).hom.restrictScalars R).comp
      (scalarTensorDegreeUnit A C D (n+1))) := by
    apply mapBifunctor.hom_ext
    intro p q h
    change p+q=n+1 at h
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change scalarTensorDegreeUnit A C D n
      ((tensorObj C D).d (n+1) n (ιTensorObj C D p q (n+1) h (u⊗ₜ[R]v))) =
        (scalarTensorComplex A C D).d (n+1) n
          (scalarTensorDegreeUnit A C D (n+1) (ιTensorObj C D p q (n+1) h (u⊗ₜ[R]v)))
    rw [scalarTensorDegreeUnit_inclusion,TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
    cases p with
    | zero =>
      obtain rfl : q=n+1 := by omega
      rw [tensorDifferential_zero_succ,tensorDifferential_zero_succ,
        scalarTensorDegreeUnit_inclusion,TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        scalarComplex_d]
      rfl
    | succ p =>
      cases q with
      | zero =>
        obtain rfl : p=n := by omega
        rw [tensorDifferential_succ_zero,tensorDifferential_succ_zero,
          scalarTensorDegreeUnit_inclusion,TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          scalarComplex_d]
        rfl
      | succ q =>
        rw [tensorDifferential_succ_succ,tensorDifferential_succ_succ,map_add,map_zsmul,
          scalarTensorDegreeUnit_inclusion,scalarTensorDegreeUnit_inclusion,
          TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          scalarComplex_d,scalarComplex_d]
        rfl
  exact congrArg (fun f=>f.hom z) he

/-- Base change commutes with the full tensor boundary over arbitrary algebras. -/
theorem scalarTensorDegreeMap_differential (n:ℕ)
    (z:(scalarComplex A (tensorObj C D)).X (n+1)) :
    scalarTensorDegreeMap A C D n ((scalarComplex A (tensorObj C D)).d (n+1) n z) =
      (scalarTensorComplex A C D).d (n+1) n (scalarTensorDegreeMap A C D (n+1) z) := by
  rw [scalarComplex_d]
  change A⊗[R](tensorObj C D).X (n+1) at z
  induction z using TensorProduct.induction_on with
  | zero =>
    exact (((scalarTensorDegreeMap A C D n).comp
      (((tensorObj C D).d (n+1) n).hom.baseChange A)).map_zero).trans
        ((((scalarTensorComplex A C D).d (n+1) n).hom.comp
          (scalarTensorDegreeMap A C D (n+1))).map_zero.symm)
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul a z =>
    change a • scalarTensorDegreeUnit A C D n ((tensorObj C D).d (n+1) n z) =
      (scalarTensorComplex A C D).d (n+1) n (a • scalarTensorDegreeUnit A C D (n+1) z)
    rw [map_smul,scalarTensorDegreeUnit_differential]

/-- Canonical scalar extension commutes with the genuine categorical tensor complex. -/
def scalarTensorComplexIso : scalarComplex A (tensorObj C D) ≅ scalarTensorComplex A C D :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n=>(scalarTensorDegreeEquiv A C D n).toModuleIso) (fun i j hij => by
      have h:j+1=i := hij
      subst i
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (scalarTensorDegreeMap_differential A C D j z).symm)

end KhanSL2.Factorization.NonnegativeCone




