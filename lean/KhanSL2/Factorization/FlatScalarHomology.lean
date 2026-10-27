module

public import KhanSL2.Factorization.ScalarComplexHomotopy
public import Mathlib.RingTheory.Flat.CategoryTheory

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Flat scalar extension preserves homology, with the ordinary tensor module
and original base-changed differential used throughout. -/
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open scoped TensorProduct
variable {R : Type} [CommRing R]
variable (A : Type) [CommRing A] [Algebra R A]

/-- The already constructed scalar-extension functor with its specified algebra. -/
abbrev scalarFunctor := NonnegativeCone.scalarModuleFunctor (R:=R) A

theorem scalarFunctor_preservesHomology [Module.Flat R A] :
    (scalarFunctor (R:=R) A).PreservesHomology := by
  apply Functor.preservesHomology_of_map_exact
  intro C hC
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hC ⊢
  exact Module.Flat.lTensor_exact A hC

attribute [local instance] scalarFunctor_preservesHomology

/-- The canonical flat base-change equivalence on categorical homology. -/
def flatShortHomologyEquiv [Module.Flat R A] (C : ShortComplex (ModuleCat R)) :
    A ⊗[R] C.homology ≃ₗ[A] (C.map (scalarFunctor A)).homology :=
  (C.mapHomologyIso (scalarFunctor A)).symm.toLinearEquiv

/-- Flat base change of the concrete cycles, with their original inclusions. -/
def flatShortCyclesEquiv [Module.Flat R A] (C : ShortComplex (ModuleCat R)) :
    A ⊗[R] LinearMap.ker C.g.hom ≃ₗ[A]
      LinearMap.ker (C.map (scalarFunctor A)).g.hom :=
  (((C.moduleCatLeftHomologyData.map (scalarFunctor A)).cyclesIso).symm ≪≫
    (C.map (scalarFunctor A)).moduleCatCyclesIso).toLinearEquiv

/-- The actual cycle inclusion after flat scalar extension. -/
theorem flatShortCyclesEquiv_val [Module.Flat R A] (C : ShortComplex (ModuleCat R))
    (z : A ⊗[R] LinearMap.ker C.g.hom) :
    (flatShortCyclesEquiv A C z).val = (LinearMap.ker C.g.hom).subtype.baseChange A z := by
  have h :
      (C.moduleCatLeftHomologyData.map (scalarFunctor A)).cyclesIso.inv ≫
        (C.map (scalarFunctor A)).moduleCatCyclesIso.hom ≫
          (C.map (scalarFunctor A)).moduleCatLeftHomologyData.i =
        (scalarFunctor A).map C.moduleCatLeftHomologyData.i := by
    rw [ShortComplex.moduleCatCyclesIso_hom_i,
      ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles]
    rfl
  exact congrArg (fun f => f.hom z) h

/-- Canonical flat base change for the literal kernel modulo incoming image. -/
def flatShortQuotientEquiv [Module.Flat R A] (C : ShortComplex (ModuleCat R)) :
    A ⊗[R] C.moduleCatLeftHomologyData.H ≃ₗ[A]
      (C.map (scalarFunctor A)).moduleCatLeftHomologyData.H :=
  (((C.moduleCatLeftHomologyData.map (scalarFunctor A)).homologyIso).symm ≪≫
    (C.map (scalarFunctor A)).moduleCatHomologyIso).toLinearEquiv

/-- Flat base change sends a represented cycle class to that same tensor cycle class. -/
theorem flatShortQuotientEquiv_mk [Module.Flat R A] (C : ShortComplex (ModuleCat R))
    (a : A) (z : LinearMap.ker C.g.hom) :
    flatShortQuotientEquiv A C (a ⊗ₜ[R] (Submodule.Quotient.mk z : C.moduleCatLeftHomologyData.H)) =
      Submodule.Quotient.mk (flatShortCyclesEquiv A C (a ⊗ₜ[R] z)) := by
  have h :
      (scalarFunctor A).map C.moduleCatLeftHomologyData.π ≫
        (C.moduleCatLeftHomologyData.map (scalarFunctor A)).homologyIso.inv ≫
          (C.map (scalarFunctor A)).moduleCatHomologyIso.hom =
      (C.moduleCatLeftHomologyData.map (scalarFunctor A)).cyclesIso.inv ≫
        (C.map (scalarFunctor A)).moduleCatCyclesIso.hom ≫
          (C.map (scalarFunctor A)).moduleCatLeftHomologyData.π := by
    change (C.moduleCatLeftHomologyData.map (scalarFunctor A)).π ≫ _ ≫ _ = _
    rw [← Category.assoc,ShortComplex.LeftHomologyData.π_comp_homologyIso_inv,
      Category.assoc,ShortComplex.π_moduleCatCyclesIso_hom]
  exact congrArg (fun f => f.hom (a ⊗ₜ[R] z)) h

end KhanSL2.Factorization
