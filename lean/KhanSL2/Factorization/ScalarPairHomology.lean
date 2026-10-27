module

public import KhanSL2.Factorization.HomologyScalarAction
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Categorical coefficient-linear homology agrees with the genuine action on
cycles modulo boundaries of the original complex differential. -/
noncomputable section
open CategoryTheory
namespace KhanSL2.Factorization
open BGG.Contraction
variable (R : Type) [CommRing R] [Algebra ℂ R]
variable {X : Type} [AddCommGroup X] [Module ℂ X]
variable (d : Module.End ℂ X) (hd : d.comp d = 0)
variable (ρ : R →ₐ[ℂ] Module.End ℂ X)
variable (hρ : ∀ r : R, (ρ r).comp d = d.comp (ρ r))

@[instance_reducible] def scalarPairChainModule : Module R X :=
  Module.compHom X ρ.toRingHom

/-- The original coefficient module, bundled to retain its specified action. -/
def scalarPairChainObject : ModuleCat R :=
  letI := scalarPairChainModule R ρ
  ModuleCat.of R X

/-- The unchanged differential, linear for its original commuting action. -/
def scalarPairDifferential : Module.End R (scalarPairChainObject R ρ) where
  toFun := d
  map_add' := map_add d
  map_smul' r x := (LinearMap.congr_fun (hρ r) x).symm

/-- The actual square-zero pair viewed over the coefficient ring. -/
def scalarPairShortComplex : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (scalarPairDifferential R d ρ hρ)
    (scalarPairDifferential R d ρ hρ) (by
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun hd x)

/-- The original induced homology action, bundled without changing the quotient. -/
def scalarPairHomologyObject : ModuleCat R :=
  letI := homologyScalarModule R d hd ρ hρ
  ModuleCat.of R (PerfectDuality.PairHomology d d hd)

/-- Taking the class of the same cycle is coefficient-linear. -/
def scalarPairCycleClass :
    LinearMap.ker (scalarPairDifferential R d ρ hρ) →ₗ[R]
      scalarPairHomologyObject R d hd ρ hρ where
  toFun z := Submodule.Quotient.mk (⟨z.val,z.property⟩ : LinearMap.ker d)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Identity on cycle representatives descends to the two actual quotients. -/
def scalarPairQuotientMap :
    (scalarPairShortComplex R d hd ρ hρ).moduleCatLeftHomologyData.H →ₗ[R]
      scalarPairHomologyObject R d hd ρ hρ :=
  (LinearMap.range (scalarPairShortComplex R d hd ρ hρ).moduleCatToCycles).liftQ
    (scalarPairCycleClass R d hd ρ hρ) (by
      rintro _ ⟨x,rfl⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨x,rfl⟩)

theorem scalarPairQuotientMap_bijective :
    Function.Bijective (scalarPairQuotientMap R d hd ρ hρ) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro u hu
      obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective
        (LinearMap.range (scalarPairShortComplex R d hd ρ hρ).moduleCatToCycles) u
      change (Submodule.Quotient.mk (⟨z.val,z.property⟩ : LinearMap.ker d) :
        PerfectDuality.PairHomology d d hd) = 0 at hu
      obtain ⟨x,hx⟩ := (Submodule.Quotient.mk_eq_zero _).mp hu
      change (Submodule.Quotient.mk z :
        (scalarPairShortComplex R d hd ρ hρ).moduleCatLeftHomologyData.H) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨x,Subtype.ext hx⟩
    · exact bot_le
  · intro u
    obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (PerfectDuality.pairBoundaries d d) u
    exact ⟨Submodule.Quotient.mk (⟨z.val,z.property⟩ :
      LinearMap.ker (scalarPairDifferential R d ρ hρ)),rfl⟩

/-- The coefficient-linear categorical homology has exactly the original
scalar action on the original complex cycle classes. -/
def scalarPairHomologyEquiv :
    (scalarPairShortComplex R d hd ρ hρ).homology ≃ₗ[R]
      scalarPairHomologyObject R d hd ρ hρ :=
  (scalarPairShortComplex R d hd ρ hρ).moduleCatHomologyIso.toLinearEquiv.trans
    (LinearEquiv.ofBijective (scalarPairQuotientMap R d hd ρ hρ)
      (scalarPairQuotientMap_bijective R d hd ρ hρ))

end KhanSL2.Factorization
