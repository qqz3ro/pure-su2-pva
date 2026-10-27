module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Evaluation formulas for the standard categorical map on module homology.
The underlying map is the existing kernel/cokernel universal-property map. -/

noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization

variable {R : Type} [CommRing R]
variable {S T : ShortComplex (ModuleCat R)}

/-- Standard module homology data for an actual short-complex map. -/
def linearModuleHomologyMapData (φ : S ⟶ T) :
    ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData :=
  default

def linearModuleCycleMap (φ : S ⟶ T) : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  (linearModuleHomologyMapData φ).φK.hom

/-- The actual standard categorical map, in the concrete cycle/boundary quotients. -/
def linearModuleQuotientHomologyMap (φ : S ⟶ T) :
    S.moduleCatLeftHomologyData.H →ₗ[R] T.moduleCatLeftHomologyData.H :=
  (linearModuleHomologyMapData φ).φH.hom

@[simp] theorem linearModuleCycleMap_val (φ : S ⟶ T) (u : LinearMap.ker S.g.hom) :
    (linearModuleCycleMap φ u).val = φ.τ₂ u.val := by
  have h := congrArg (fun f => f.hom u) (linearModuleHomologyMapData φ).commi
  exact h

@[simp] theorem linearModuleQuotientHomologyMap_mk (φ : S ⟶ T) (u : LinearMap.ker S.g.hom) :
    linearModuleQuotientHomologyMap φ (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (linearModuleCycleMap φ u) := by
  have h := congrArg (fun f => f.hom u) (linearModuleHomologyMapData φ).commπ
  exact h

/-- Bijectivity of the concrete standard homology map is a categorical quasi-isomorphism. -/
theorem quasiIso_of_linearModuleQuotientHomologyMap_bijective (φ : S ⟶ T)
    (h : Function.Bijective (linearModuleQuotientHomologyMap φ)) : ShortComplex.QuasiIso φ := by
  have : IsIso (linearModuleHomologyMapData φ).φH :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  rw [ShortComplex.quasiIso_iff,(linearModuleHomologyMapData φ).homologyMap_eq]
  infer_instance

end KhanSL2.Factorization
