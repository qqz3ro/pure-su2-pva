module

public import KhanSL2.Factorization.ScalarComplexHomotopy
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Homology.Monoidal

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

local instance scalarTensorRestrictModule (X : ModuleCat A) : Module R X :=
  Module.compHom X (algebraMap R A)

local instance scalarTensorRestrictTower (X : ModuleCat A) : IsScalarTower R A X where
  smul_assoc r a x := by
    change (r • a) • x = (algebraMap R A r) • (a • x)
    rw [Algebra.smul_def, mul_smul]

local instance scalarTensorRestrictComm (X : ModuleCat A) : SMulCommClass R A X :=
  IsScalarTower.to_smulCommClass

/-- The tensor of scalar-extended complexes, with its actual degree-sum terms. -/
abbrev scalarTensorComplex := tensorObj (scalarComplex A C) (scalarComplex A D)

/-- The canonical unit map on the degree sum before extending its scalars. -/
def scalarTensorDegreeUnit (n : ℕ) :
    (tensorObj C D).X n →ₗ[R] (scalarTensorComplex A C D).X n :=
  (mapBifunctorDesc (K₁:=C) (K₂:=D) (F:=MonoidalCategory.curriedTensor (ModuleCat R))
    (c:=ComplexShape.down ℕ) (j:=n)
    (A:=ModuleCat.of R ((scalarTensorComplex A C D).X n))
    (fun p q h => ModuleCat.ofHom
      ((((ιTensorObj (scalarComplex A C) (scalarComplex A D) p q n h).hom.comp
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q)).toLinearMap).restrictScalars R).comp
          (TensorProduct.mk R A (C.X p ⊗[R] D.X q) 1)))).hom

@[simp] theorem scalarTensorDegreeUnit_inclusion (p q n : ℕ) (h:p+q=n)
    (z:C.X p ⊗[R] D.X q) :
    scalarTensorDegreeUnit A C D n (ιTensorObj C D p q n h z) =
      ιTensorObj (scalarComplex A C) (scalarComplex A D) p q n h
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q) (1⊗ₜ[R]z)) := by
  have he := ι_mapBifunctorDesc (K₁:=C) (K₂:=D)
    (F:=MonoidalCategory.curriedTensor (ModuleCat R)) (c:=ComplexShape.down ℕ)
    (j:=n) (A:=ModuleCat.of R ((scalarTensorComplex A C D).X n))
    (fun p q h => ModuleCat.ofHom
      ((((ιTensorObj (scalarComplex A C) (scalarComplex A D) p q n h).hom.comp
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q)).toLinearMap).restrictScalars R).comp
          (TensorProduct.mk R A (C.X p ⊗[R] D.X q) 1))) p q h
  exact congrArg (fun f => f.hom z) he

/-- Scalar extension commutes with the tensor degree sum, on the specified maps. -/
def scalarTensorDegreeMap (n:ℕ) :
    A⊗[R](tensorObj C D).X n →ₗ[A] (scalarTensorComplex A C D).X n :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun a := a • scalarTensorDegreeUnit A C D n
      map_add' a b := add_smul a b _
      map_smul' a b := mul_smul a b _ }

@[simp] theorem scalarTensorDegreeMap_tmul_inclusion (p q n:ℕ) (h:p+q=n)
    (a:A) (z:C.X p⊗[R]D.X q) :
    scalarTensorDegreeMap A C D n (a⊗ₜ[R]ιTensorObj C D p q n h z) =
      ιTensorObj (scalarComplex A C) (scalarComplex A D) p q n h
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q) (a⊗ₜ[R]z)) := by
  change a • scalarTensorDegreeUnit A C D n (ιTensorObj C D p q n h z) = _
  rw [scalarTensorDegreeUnit_inclusion]
  let f : A⊗[R](C.X p⊗[R]D.X q) →ₗ[A] (scalarTensorComplex A C D).X n :=
    (ιTensorObj (scalarComplex A C) (scalarComplex A D) p q n h).hom.comp
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q)).toLinearMap
  change a • f (1⊗ₜ[R]z) = f (a⊗ₜ[R]z)
  rw [← f.map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
/-- Its inverse is the sum of the inverse base-change tensor maps. -/
def scalarTensorDegreeInverse (n:ℕ) :
    (scalarTensorComplex A C D).X n →ₗ[A] A⊗[R](tensorObj C D).X n :=
  (mapBifunctorDesc (K₁:=scalarComplex A C) (K₂:=scalarComplex A D)
    (F:=MonoidalCategory.curriedTensor (ModuleCat A)) (c:=ComplexShape.down ℕ) (j:=n)
    (A:=ModuleCat.of A (A⊗[R](tensorObj C D).X n))
    (fun p q h => ModuleCat.ofHom
      (((ιTensorObj C D p q n h).hom.baseChange A).comp
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q)).symm.toLinearMap))).hom

@[simp] theorem scalarTensorDegreeInverse_inclusion (p q n:ℕ) (h:p+q=n)
    (z:(scalarComplex A C).X p⊗[A](scalarComplex A D).X q) :
    scalarTensorDegreeInverse A C D n
      (ιTensorObj (scalarComplex A C) (scalarComplex A D) p q n h z) =
      ((ιTensorObj C D p q n h).hom.baseChange A)
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q)).symm z) := by
  have he := ι_mapBifunctorDesc (K₁:=scalarComplex A C) (K₂:=scalarComplex A D)
    (F:=MonoidalCategory.curriedTensor (ModuleCat A)) (c:=ComplexShape.down ℕ) (j:=n)
    (A:=ModuleCat.of A (A⊗[R](tensorObj C D).X n))
    (fun p q h => ModuleCat.ofHom
      (((ιTensorObj C D p q n h).hom.baseChange A).comp
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A (C.X p) (D.X q)).symm.toLinearMap)) p q h
  exact congrArg (fun f => f.hom z) he

end KhanSL2.Factorization.NonnegativeCone





