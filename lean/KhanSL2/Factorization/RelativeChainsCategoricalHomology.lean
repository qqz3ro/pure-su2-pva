module

public import KhanSL2.Factorization.RelativeChainsHomology
public import Mathlib.Algebra.Homology.QuasiIso

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Evaluation formulas for the standard categorical map on module homology.
The underlying map is the existing kernel/cokernel universal-property map. -/

noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization

variable {S T : ShortComplex (ModuleCat ℂ)}

/-- Standard module homology data for an actual short-complex map. -/
def moduleHomologyMapData (φ : S ⟶ T) :
    ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData :=
  default

def moduleCycleMap (φ : S ⟶ T) : LinearMap.ker S.g.hom →ₗ[ℂ] LinearMap.ker T.g.hom :=
  (moduleHomologyMapData φ).φK.hom

/-- The actual standard categorical map, in the concrete cycle/boundary quotients. -/
def moduleQuotientHomologyMap (φ : S ⟶ T) :
    S.moduleCatLeftHomologyData.H →ₗ[ℂ] T.moduleCatLeftHomologyData.H :=
  (moduleHomologyMapData φ).φH.hom

@[simp] theorem moduleCycleMap_val (φ : S ⟶ T) (u : LinearMap.ker S.g.hom) :
    (moduleCycleMap φ u).val = φ.τ₂ u.val := by
  have h := congrArg (fun f => f.hom u) (moduleHomologyMapData φ).commi
  exact h

@[simp] theorem moduleQuotientHomologyMap_mk (φ : S ⟶ T) (u : LinearMap.ker S.g.hom) :
    moduleQuotientHomologyMap φ (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk (moduleCycleMap φ u) := by
  have h := congrArg (fun f => f.hom u) (moduleHomologyMapData φ).commπ
  exact h

/-- Bijectivity of the concrete standard homology map is a categorical quasi-isomorphism. -/
theorem quasiIso_of_moduleQuotientHomologyMap_bijective (φ : S ⟶ T)
    (h : Function.Bijective (moduleQuotientHomologyMap φ)) : ShortComplex.QuasiIso φ := by
  have : IsIso (moduleHomologyMapData φ).φH :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  rw [ShortComplex.quasiIso_iff,(moduleHomologyMapData φ).homologyMap_eq]
  infer_instance

end KhanSL2.Factorization
