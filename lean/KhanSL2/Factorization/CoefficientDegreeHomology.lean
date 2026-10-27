module

public import KhanSL2.Factorization.HomogeneousCoefficientScalars
public import KhanSL2.Factorization.BalancedTensorCycleDegrees
public import KhanSL2.Factorization.RelativeChainsHomology

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open CategoryTheory
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientDegreeModule coefficientDegreeIsScalarTower coefficientDegreeSMulCommClass
  coefficientHomogeneousHomologyModule coefficientHomogeneousHomologyIsScalarTower
  coefficientHomogeneousHomologySMulCommClass

abbrev coefficientDegreeShortComplex (p : ℕ) : ShortComplex (ModuleCat R) :=
  (coefficientRelativeComplex R M).sc' (p+1) p (p-1)

/-- This is the original class of a homogeneous CE cycle. -/
def coefficientDegreeCycleClass (p : ℕ) :
    LinearMap.ker (coefficientDegreeShortComplex R M p).g.hom →ₗ[R] Homology M p where
  toFun z := Submodule.Quotient.mk (⟨z.val.val,z.val.property,
    (coefficientDegree_cycle_iff R M p z.val).mp z.property⟩ : (window M p).cycles)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A categorical boundary is exactly the corresponding original CE boundary. -/
theorem coefficientDegreeCycleClass_boundaries (p : ℕ) :
    LinearMap.range (coefficientDegreeShortComplex R M p).moduleCatToCycles ≤
      LinearMap.ker (coefficientDegreeCycleClass R M p) := by
  rintro _ ⟨w,rfl⟩
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨w.val,w.property,?_⟩
  change differential M w.val =
    ((coefficientRelativeComplex R M).d (p+1) p w).val
  rw [coefficientRelativeComplex_d]
  rfl

def coefficientDegreeQuotientMap (p : ℕ) :
    (coefficientDegreeShortComplex R M p).moduleCatLeftHomologyData.H →ₗ[R] Homology M p :=
  (LinearMap.range (coefficientDegreeShortComplex R M p).moduleCatToCycles).liftQ
    (coefficientDegreeCycleClass R M p) (coefficientDegreeCycleClass_boundaries R M p)

theorem coefficientDegreeQuotientMap_bijective (p : ℕ) :
    Function.Bijective (coefficientDegreeQuotientMap R M p) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro q hq
    obtain ⟨z,rfl⟩ := (Submodule.mkQ_surjective
      (LinearMap.range (coefficientDegreeShortComplex R M p).moduleCatToCycles)) q
    change Submodule.Quotient.mk (⟨z.val.val,z.val.property,
      (coefficientDegree_cycle_iff R M p z.val).mp z.property⟩ : (window M p).cycles) = 0 at hq
    obtain ⟨w,hw,hwz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨(⟨w,hw⟩ : degree M (p+1)),?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((coefficientRelativeComplex R M).d (p+1) p ⟨w,hw⟩).val = z.val.val
    rw [coefficientRelativeComplex_d]
    exact hwz
  · intro q
    obtain ⟨z,rfl⟩ := (Submodule.mkQ_surjective (window M p).boundaries) q
    refine ⟨Submodule.Quotient.mk
      (⟨⟨z.val,z.property.1⟩,(coefficientDegree_cycle_iff R M p _).mpr z.property.2⟩ :
        LinearMap.ker (coefficientDegreeShortComplex R M p).g.hom),?_⟩
    rfl

/-- The original coefficient action on the native homogeneous quotient agrees
with the categorical homology of the original coefficient-linear CE complex. -/
def coefficientComplexHomologyEquiv (p : ℕ) :
    (coefficientRelativeComplex R M).homology p ≃ₗ[R] Homology M p :=
  (((coefficientRelativeComplex R M).homologyIsoSc' (p+1) p (p-1)
    (ChainComplex.prev ℕ p) (by cases p <;> simp)).toLinearEquiv.trans
      (coefficientDegreeShortComplex R M p).moduleCatHomologyIso.toLinearEquiv).trans
        (LinearEquiv.ofBijective (coefficientDegreeQuotientMap R M p)
          (coefficientDegreeQuotientMap_bijective R M p))

end KhanSL2.Factorization
