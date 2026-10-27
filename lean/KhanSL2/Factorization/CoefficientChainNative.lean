module

public import KhanSL2.Factorization.CoefficientChainRestriction
public import KhanSL2.SymmetricFamily.FactorCurrent
public import KhanSL2.Factorization.ShuffleEquivalences

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open CategoryTheory HomologicalComplex
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

variable (M : Type) [AddCommGroup M] [Module ℂ M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent ℂ M]

/-- Over ℂ, the coefficient-linear and native CE complexes agree literally on
represented chains; this is their explicit identity isomorphism. -/
def coefficientNativeComplexIso : coefficientRelativeComplex ℂ M ≅ complex M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (ModuleCat.restrictScalarsId'App (algebraMap ℂ ℂ) rfl
      ((coefficientRelativeComplex ℂ M).X j)).symm ≪≫
        (coefficientDegreeRestriction ℂ M j).toModuleIso) (fun i j hij => by
      have h : j+1=i := hij
      subst i
      rw [complex_d,coefficientRelativeComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      rfl)

@[simp] theorem coefficientNativeComplexIso_hom_f_apply (j : ℕ)
    (z:(coefficientRelativeComplex ℂ M).X j) :
    (coefficientNativeComplexIso M).hom.f j z = z := rfl

@[simp] theorem coefficientNativeComplexIso_inv_f_apply (j : ℕ)
    (z:(complex M).X j) :
    (coefficientNativeComplexIso M).inv.f j z = z := rfl

end KhanSL2.Factorization
