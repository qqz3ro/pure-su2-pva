module

public import KhanSL2.Factorization.ScalarComplexHomotopy

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization.NonnegativeCone

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]
variable {C D E : ChainComplex (ModuleCat R) ℕ}

@[simp] theorem scalarMap_comp (f : C ⟶ D) (g : D ⟶ E) :
    scalarMap S (f ≫ g) = scalarMap S f ≫ scalarMap S g := by
  ext j : 1
  apply ModuleCat.hom_ext
  exact LinearMap.baseChange_comp (f.f j).hom (g.f j).hom

@[simp] theorem scalarMap_id (C : ChainComplex (ModuleCat R) ℕ) :
    scalarMap S (𝟙 C) = 𝟙 (scalarComplex S C) := by
  ext j : 1
  apply ModuleCat.hom_ext
  exact LinearMap.baseChange_id

/-- An actual chain isomorphism remains an isomorphism after every scalar extension. -/
def scalarComplexIso (e : C ≅ D) : scalarComplex S C ≅ scalarComplex S D where
  hom := scalarMap S e.hom
  inv := scalarMap S e.inv
  hom_inv_id := by rw [← scalarMap_comp,e.hom_inv_id,scalarMap_id]
  inv_hom_id := by rw [← scalarMap_comp,e.inv_hom_id,scalarMap_id]

/-- Homotopy-model comparisons survive scalar extension, including at nonflat fibres. -/
theorem scalarMap_homotopyHom_quasiIso (e : HomotopyEquiv C D) :
    QuasiIso (scalarMap S e.hom) := by
  rw [← scalarHomotopyEquiv_hom]
  infer_instance

theorem scalarMap_homotopyInv_quasiIso (e : HomotopyEquiv C D) :
    QuasiIso (scalarMap S e.inv) := by
  rw [← scalarHomotopyEquiv_inv]
  infer_instance

end KhanSL2.Factorization.NonnegativeCone

