module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.QuasiIso

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace KhanSL2.Factorization.QuasiIsoElements

variable {R : Type*} [CommRing R]
variable {S T : ShortComplex (ModuleCat R)}

/-- The familiar cycle-and-boundary criterion, for the actual canonical
homology map of a short complex. -/
theorem quasiIso_of_cycles (φ : S ⟶ T)
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, φ.τ₂ x - y = T.f z)
    (hinj : ∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, φ.τ₂ x = T.f z) → ∃ w : S.X₁, S.f w = x) :
    ShortComplex.QuasiIso φ := by
  let γ : ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData
    T.moduleCatLeftHomologyData := default
  have hk (x : LinearMap.ker S.g.hom) :
      ((show LinearMap.ker T.g.hom from γ.φK.hom x) : T.X₂) = φ.τ₂ x := by
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom γ.commi) x
  have hπ (x : LinearMap.ker S.g.hom) :
      γ.φH.hom (S.moduleCatLeftHomologyData.π.hom x) =
        T.moduleCatLeftHomologyData.π.hom (γ.φK.hom x) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom γ.commπ) x
  apply γ.quasiIso_iff.mpr
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective γ.φH.hom
  constructor
  · apply (injective_iff_map_eq_zero γ.φH.hom).mpr
    intro q hq
    obtain ⟨x,rfl⟩ := (show Function.Surjective S.moduleCatLeftHomologyData.π.hom from Submodule.mkQ_surjective _) q
    change LinearMap.ker S.g.hom at x
    rw [hπ] at hq
    change Submodule.Quotient.mk (γ.φK.hom x) = 0 at hq
    obtain ⟨z,hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    have hx : φ.τ₂ (x : S.X₂) = T.f z := by
      rw [← hk]
      exact (congrArg Subtype.val hz).symm
    obtain ⟨w,hw⟩ := hinj x x.property ⟨z,hx⟩
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨w,Subtype.ext hw⟩
  · intro q
    obtain ⟨y,rfl⟩ := (show Function.Surjective T.moduleCatLeftHomologyData.π.hom from Submodule.mkQ_surjective _) q
    change LinearMap.ker T.g.hom at y
    obtain ⟨x,hx,z,hz⟩ := hsurj y y.property
    refine ⟨S.moduleCatLeftHomologyData.π.hom ⟨x,hx⟩,?_⟩
    rw [hπ]
    change Submodule.Quotient.mk (γ.φK.hom ⟨x,hx⟩) = Submodule.Quotient.mk y
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨z,Subtype.ext ?_⟩
    change T.f z = ((show LinearMap.ker T.g.hom from γ.φK.hom ⟨x,hx⟩) : T.X₂) - y
    rw [hk]
    exact hz.symm

/-- Conversely, a quasi-isomorphism lifts cycles modulo boundaries and
reflects boundaries. -/
theorem cycles_of_quasiIso (φ : S ⟶ T) [ShortComplex.QuasiIso φ] :
    (∀ y : T.X₂, T.g y = 0 →
      ∃ x : S.X₂, S.g x = 0 ∧ ∃ z : T.X₁, φ.τ₂ x - y = T.f z) ∧
    (∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, φ.τ₂ x = T.f z) → ∃ w : S.X₁, S.f w = x) := by
  let γ : ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData
    T.moduleCatLeftHomologyData := default
  have hk (x : LinearMap.ker S.g.hom) :
      ((show LinearMap.ker T.g.hom from γ.φK.hom x) : T.X₂) = φ.τ₂ x :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom γ.commi) x
  have hπ (x : LinearMap.ker S.g.hom) :
      γ.φH.hom (S.moduleCatLeftHomologyData.π.hom x) =
        T.moduleCatLeftHomologyData.π.hom (γ.φK.hom x) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom γ.commπ) x
  have hi : IsIso γ.φH := γ.quasiIso_iff.mp inferInstance
  have hb : Function.Bijective γ.φH.hom := (ConcreteCategory.isIso_iff_bijective γ.φH).mp hi
  constructor
  · intro y hy
    obtain ⟨q,hq⟩ := hb.surjective (T.moduleCatLeftHomologyData.π.hom ⟨y,hy⟩)
    obtain ⟨x,rfl⟩ := (show Function.Surjective S.moduleCatLeftHomologyData.π.hom from Submodule.mkQ_surjective _) q
    change LinearMap.ker S.g.hom at x
    rw [hπ] at hq
    change Submodule.Quotient.mk (γ.φK.hom x) = Submodule.Quotient.mk ⟨y,hy⟩ at hq
    obtain ⟨z,hz⟩ := (Submodule.Quotient.eq _).mp hq
    refine ⟨x,x.property,z,?_⟩
    have hz' := congrArg Subtype.val hz
    change T.f z = ((show LinearMap.ker T.g.hom from γ.φK.hom x) : T.X₂) - y at hz'
    rw [hk] at hz'
    exact hz'.symm
  · intro x hx ⟨z,hz⟩
    have hq : T.moduleCatLeftHomologyData.π.hom (γ.φK.hom ⟨x,hx⟩) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨z,Subtype.ext ?_⟩
      change T.f z = ((show LinearMap.ker T.g.hom from γ.φK.hom ⟨x,hx⟩) : T.X₂)
      rw [hk]
      exact hz.symm
    have hzero : S.moduleCatLeftHomologyData.π.hom ⟨x,hx⟩ = 0 := by
      apply hb.injective
      rw [hπ,map_zero]
      exact hq
    obtain ⟨w,hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hzero
    exact ⟨w,congrArg Subtype.val hw⟩
end KhanSL2.Factorization.QuasiIsoElements
