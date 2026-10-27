module

public import KhanSL2.Factorization.CoefficientChainMaps
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Additive

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory
namespace KhanSL2.Factorization
open BGG BGGBridge SymmetricFamily

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower coefficientChainSMulCommClass
  coefficientDegreeModule coefficientDegreeIsScalarTower coefficientDegreeSMulCommClass

theorem coefficientDegree_algebraMap_smul (j : ℕ) (c : ℂ) (z : degree M j) :
    (algebraMap ℂ A c) • z = c • z := algebraMap_smul A c z

/-- Restriction of the original coefficient action recovers the original
complex-vector-space degree group, by the identity on represented chains. -/
def coefficientDegreeRestriction (j : ℕ) :
    (ModuleCat.restrictScalars (algebraMap ℂ A)).obj ((coefficientRelativeComplex A M).X j)
      ≃ₗ[ℂ] (complex M).X j where
  toFun z := z
  invFun z := z
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c z := coefficientDegree_algebraMap_smul A M j c z

/-- The original coefficient-linear CE complex restricts to the original CE
complex, with no replacement of its differential or underlying classes. -/
def coefficientComplexRestriction :
    ((ModuleCat.restrictScalars (algebraMap ℂ A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (coefficientRelativeComplex A M) ≅ complex M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (coefficientDegreeRestriction A M j).toModuleIso) (fun i j hij => by
      have h : j+1=i := hij
      subst i
      rw [complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change degree M (j+1) at z
      change (degreeDifferential M j z) =
        (coefficientRelativeComplex A M).d (j+1) j z
      rw [coefficientRelativeComplex_d]
      rfl)

@[simp] theorem coefficientComplexRestriction_hom_f_apply (j : ℕ)
    (z : (((ModuleCat.restrictScalars (algebraMap ℂ A)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (coefficientRelativeComplex A M)).X j) :
    (coefficientComplexRestriction A M).hom.f j z = z := rfl

end KhanSL2.Factorization

