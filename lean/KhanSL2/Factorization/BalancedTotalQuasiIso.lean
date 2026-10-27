module

public import KhanSL2.Factorization.BalancedTensorCycleDegrees
public import KhanSL2.Factorization.BalancedTotalHomology
public import KhanSL2.Factorization.QuasiIsoElements

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open CategoryTheory HomologicalComplex
open scoped TensorProduct DirectSum
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N L : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
  [AddCommGroup L] [Module ℂ L] [Module A L] [IsScalarTower ℂ A L]
  [LieRingModule Current L] [LieModule ℂ Current L] [CoefficientLinearCurrent A L]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientDegreeModule coefficientDegreeIsScalarTower coefficientDegreeSMulCommClass
  coefficientTotalHomologyModule coefficientTotalHomologyIsScalarTower coefficientTotalHomologySMulCommClass

variable (F : RelativeChains L →ₗ[A] RelativeChains M ⊗[A] RelativeChains N)
variable (α : coefficientRelativeComplex A L ⟶ balancedTensorComplex A M N)
variable (hα : ∀ j (u : degree L j), balancedTensorDegreeForget A M N j (α.f j u) = F u.val)

include hα

/-- The given degreewise comparison retains the original total degree projection. -/
theorem balancedTensorComparison_component (j : ℕ) (u : RelativeChains L) :
    balancedTensorDegreeComponent A M N j (F u) =
      α.f j (coefficientDegreeComponentLinear A L j u) := by
  obtain ⟨v,rfl⟩ := (degreeSumEquiv L).surjective u
  induction v using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | of q u =>
    rw [degreeSumEquiv_of,← hα q u]
    by_cases h : j=q
    · subst q
      rw [balancedTensorDegreeComponent_forget]
      change α.f j u = α.f j (degreeComponent L j u.val)
      rw [degreeComponent_subtype]
    · rw [balancedTensorDegreeComponent_forget_ne A M N h]
      change 0 = α.f j (degreeComponent L j u.val)
      rw [degreeComponent_subtype_ne L h,map_zero]

variable (hF : ∀ z, F (differential L z) = balancedTensorDifferential A M N (F z))

/-- Total bijectivity of this specified balanced comparison implies its
quasi-isomorphism in every exterior degree. No homology base-change is presumed. -/
theorem quasiIso_of_balancedTotalHomology_bijective
    (htotal : Function.Bijective (balancedTotalComparisonMap A M N L F hF)) : QuasiIso α := by
  let φtotal := balancedTotalComparisonShortMap A M N L F hF
  have htotal' : Function.Bijective (linearModuleQuotientHomologyMap φtotal) := by
    have he : linearModuleQuotientHomologyMap φtotal =
        (balancedTotalComparisonMap A M N L F hF).comp (coefficientTotalQuotientEquiv A L).toLinearMap := by
      apply LinearMap.ext
      intro u
      change linearModuleQuotientHomologyMap φtotal u =
        linearModuleQuotientHomologyMap φtotal
          ((coefficientTotalQuotientEquiv A L).symm (coefficientTotalQuotientEquiv A L u))
      rw [LinearEquiv.symm_apply_apply]
    rw [he]
    exact htotal.comp (coefficientTotalQuotientEquiv A L).bijective
  let := quasiIso_of_linearModuleQuotientHomologyMap_bijective φtotal htotal'
  obtain ⟨hsurj,hinj⟩ := QuasiIsoElements.cycles_of_quasiIso φtotal
  refine ⟨fun j => ?_⟩
  rw [quasiIsoAt_iff' α (j+1) j (j-1) (ChainComplex.prev ℕ j) (by
    cases j with
    | zero => exact ChainComplex.next_nat_zero
    | succ j => simpa only [Nat.add_one_sub_one] using ChainComplex.next_nat_succ j)]
  apply QuasiIsoElements.quasiIso_of_cycles
  · intro y hy
    have hy' := (balancedTensorDegree_cycle_iff A M N j y).mp hy
    obtain ⟨x,hx,z,hz⟩ := hsurj (balancedTensorDegreeForget A M N j y) hy'
    refine ⟨coefficientDegreeComponentLinear A L j x,?_,balancedTensorDegreeComponent A M N (j+1) z,?_⟩
    · apply (coefficientDegree_cycle_iff A L j _).mpr
      exact degreeProjection_mem_ker L j hx
    · have he := congrArg (balancedTensorDegreeComponent A M N j) hz
      change balancedTensorDegreeComponent A M N j
        (F x - balancedTensorDegreeForget A M N j y) =
          balancedTensorDegreeComponent A M N j (balancedTensorDifferential A M N z) at he
      rw [map_sub,balancedTensorComparison_component A M N L F α hα,
        balancedTensorDegreeComponent_forget,balancedTensorDegreeComponent_differential] at he
      exact he
  · intro x hx ⟨z,hz⟩
    have hx' := (coefficientDegree_cycle_iff A L j x).mp hx
    have hz' : F x.val = balancedTensorDifferential A M N
        (balancedTensorDegreeForget A M N (j+1) z) := by
      have he := congrArg (balancedTensorDegreeForget A M N j) hz
      have hd := congrArg (fun f => f.hom z) (balancedTensorDegreeForget_differential A M N j)
      change balancedTensorDegreeForget A M N j (α.f j x) =
        balancedTensorDegreeForget A M N j ((balancedTensorComplex A M N).d (j+1) j z) at he
      rw [hα] at he
      exact he.trans hd
    obtain ⟨w,hw⟩ := hinj x.val hx' ⟨balancedTensorDegreeForget A M N (j+1) z,hz'⟩
    refine ⟨coefficientDegreeComponentLinear A L (j+1) w,?_⟩
    change (coefficientRelativeComplex A L).d (j+1) j
      (coefficientDegreeComponentLinear A L (j+1) w) = x
    rw [coefficientRelativeComplex_d]
    apply Subtype.ext
    change differential L (degreeProjection L (j+1) w) = x.val
    change differential L w = x.val at hw
    rw [← degreeProjection_differential L j,hw,degreeProjection_of_mem L x.property]

end KhanSL2.Factorization


