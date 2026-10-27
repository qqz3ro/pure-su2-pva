module

public import KhanSL2.Factorization.RelativeChainsScalarDegrees
public import KhanSL2.Factorization.NonnegativeConeBaseChange

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily NonnegativeCone

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]
variable (A : Type) [CommRing A] [Algebra R A] [Algebra ℂ A] [IsScalarTower ℂ R A]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientDegreeModule coefficientDegreeIsScalarTower
  coefficientDegreeSMulCommClass

/-- The canonical scalar-chain equivalence intertwines the unchanged CE boundary. -/
theorem relativeChainsScalarMap_differential (z : A ⊗[R] RelativeChains M) :
    relativeChainsScalarMap R M A ((coefficientDifferentialLinear R M).baseChange A z) =
      differential (CoefficientBaseChange R M A) (relativeChainsScalarMap R M A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add,hz,hw]
  | tmul a z =>
    change a • coefficientMap (coefficientBaseChangeUnit R M A).toLinearMap
      (constantEquivariant_of_lieHom (coefficientBaseChangeUnit R M A)) (differential M z) =
      differential (CoefficientBaseChange R M A)
        (a • coefficientMap (coefficientBaseChangeUnit R M A).toLinearMap
          (constantEquivariant_of_lieHom (coefficientBaseChangeUnit R M A)) z)
    rw [differential_coefficient_smul A (CoefficientBaseChange R M A),coefficientMap_differential]

theorem relativeChainsScalarDegreeMap_differential (j : ℕ) (z : A ⊗[R] degree M (j+1)) :
    relativeChainsScalarDegreeMap R M A j
      ((coefficientDegreeDifferentialLinear R M j).baseChange A z) =
      coefficientDegreeDifferentialLinear A (CoefficientBaseChange R M A) j
        (relativeChainsScalarDegreeMap R M A (j+1) z) := by
  apply Subtype.ext
  change relativeChainsScalarMap R M A
    ((coefficientDegreeInclusionLinear R M j).baseChange A
      ((coefficientDegreeDifferentialLinear R M j).baseChange A z)) =
    differential (CoefficientBaseChange R M A)
      (relativeChainsScalarMap R M A
        ((coefficientDegreeInclusionLinear R M (j+1)).baseChange A z))
  have h : (coefficientDegreeInclusionLinear R M j).comp
      (coefficientDegreeDifferentialLinear R M j) =
      (coefficientDifferentialLinear R M).comp (coefficientDegreeInclusionLinear R M (j+1)) := rfl
  have hA := congrArg (fun f => f.baseChange A) h
  simp only [LinearMap.baseChange_comp] at hA
  have he := LinearMap.congr_fun hA z
  change (coefficientDegreeInclusionLinear R M j).baseChange A
      ((coefficientDegreeDifferentialLinear R M j).baseChange A z) = _ at he
  rw [he,LinearMap.comp_apply,relativeChainsScalarMap_differential]

/-- Actual coefficient base change agrees with scalar extension of the relative
CE complex before taking homology, without flatness restrictions. -/
def relativeChainsScalarComplexIso :
    scalarComplex A (coefficientRelativeComplex R M) ≅
      coefficientRelativeComplex A (CoefficientBaseChange R M A) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (relativeChainsScalarDegreeEquiv R M A j).toModuleIso)
    (fun i j hij => by
      have h : j+1=i := hij
      subst i
      rw [scalarComplex_d,coefficientRelativeComplex_d,coefficientRelativeComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (relativeChainsScalarDegreeMap_differential R M A j z).symm)

end KhanSL2.Factorization


