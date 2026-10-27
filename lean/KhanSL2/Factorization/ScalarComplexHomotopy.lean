module

public import KhanSL2.Factorization.NonnegativeConeBaseChange
public import Mathlib.Algebra.Homology.Homotopy

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization.NonnegativeCone

variable {R : Type} [CommRing R]
variable (A : Type) [CommRing A] [Algebra R A]

/-- Ordinary scalar extension as an additive functor on actual module objects. -/
def scalarModuleFunctor : ModuleCat R ⥤ ModuleCat A where
  obj M := ModuleCat.of A (A ⊗[R] M)
  map f := ModuleCat.ofHom (f.hom.baseChange A)
  map_id M := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.baseChange_comp _ _

instance scalarModuleFunctor_additive : (scalarModuleFunctor (R:=R) A).Additive where
  map_add {X Y} {f g} := by
    apply ModuleCat.hom_ext
    change (f.hom + g.hom).baseChange A = f.hom.baseChange A + g.hom.baseChange A
    exact LinearMap.baseChange_add f.hom g.hom

/-- The chain-level functor agrees with the existing consecutive-map scalar complex. -/
def scalarModuleComplexIso (C : ChainComplex (ModuleCat R) ℕ) :
    ((scalarModuleFunctor A).mapHomologicalComplex (ComplexShape.down ℕ)).obj C ≅ scalarComplex A C :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    have h : j+1=i := hij
    subst i
    rw [scalarComplex_d]
    apply ModuleCat.hom_ext
    change ((C.d (j+1) j).hom.baseChange A).comp LinearMap.id =
      LinearMap.id.comp ((C.d (j+1) j).hom.baseChange A)
    simp)

/-- Every genuine chain homotopy equivalence survives arbitrary scalar extension. -/
def scalarHomotopyEquiv {C D : ChainComplex (ModuleCat R) ℕ} (h : HomotopyEquiv C D) :
    HomotopyEquiv (scalarComplex A C) (scalarComplex A D) :=
  (HomotopyEquiv.ofIso (scalarModuleComplexIso A C).symm).trans
    (((scalarModuleFunctor A).mapHomotopyEquiv h).trans
      (HomotopyEquiv.ofIso (scalarModuleComplexIso A D)))

theorem scalarHomotopyEquiv_hom {C D : ChainComplex (ModuleCat R) ℕ} (h : HomotopyEquiv C D) :
    (scalarHomotopyEquiv A h).hom = scalarMap A h.hom := by
  ext j : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

theorem scalarHomotopyEquiv_inv {C D : ChainComplex (ModuleCat R) ℕ} (h : HomotopyEquiv C D) :
    (scalarHomotopyEquiv A h).inv = scalarMap A h.inv := by
  ext j : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

end KhanSL2.Factorization.NonnegativeCone



