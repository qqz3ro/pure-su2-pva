module

public import KhanSL2.Factorization.ResultantChartFactorFlat
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open TensorProduct
namespace KhanSL2.Factorization.ChartBridge

instance productCoefficients_finiteType (r s : ℕ) :
    Algebra.FiniteType ℂ (ProductCoefficients r s) := by
  change Algebra.FiniteType ℂ (Depth.RB r ⊗[ℂ] Depth.RB s)
  exact Algebra.FiniteType.trans (S := Depth.RB r) inferInstance inferInstance
instance productChart_finiteType (r s : ℕ) : Algebra.FiniteType ℂ (ProductChart r s) :=
  Algebra.FiniteType.trans (S := ProductCoefficients r s) inferInstance inferInstance

section ClosedPoints
variable {A : Type*} [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]

/-- Zariski's lemma and algebraic closedness identify every maximal residue
field of a finite-type complex algebra, through its actual constant map. -/
def complexResidueEquiv (p : Ideal A) [p.IsMaximal] : ℂ ≃ₐ[ℂ] p.ResidueField := by
  let : Algebra.FiniteType ℂ p.ResidueField :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  let := finite_of_finite_type_of_isJacobsonRing ℂ p.ResidueField
  exact AlgEquiv.ofBijective (Algebra.ofId ℂ p.ResidueField)
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- The complex point associated to a maximal ideal, not an arbitrary equality
between its residue field and ℂ. -/
def closedPoint (p : Ideal A) [p.IsMaximal] : A →ₐ[ℂ] ℂ :=
  (complexResidueEquiv p).symm.toAlgHom.comp (IsScalarTower.toAlgHom ℂ A p.ResidueField)

@[simp] theorem complexResidueEquiv_closedPoint (p : Ideal A) [p.IsMaximal] (a : A) :
    complexResidueEquiv p (closedPoint p a) = algebraMap A p.ResidueField a := by
  simp only [closedPoint,AlgHom.comp_apply,AlgEquiv.toAlgHom_eq_coe,AlgEquiv.coe_algHom,
    IsScalarTower.coe_toAlgHom,AlgEquiv.apply_symm_apply]
  rfl

theorem closedPoint_eq_zero_iff (p : Ideal A) [p.IsMaximal] (a : A) :
    closedPoint p a = 0 ↔ a ∈ p := by
  rw [← (complexResidueEquiv p).injective.eq_iff,map_zero,
    complexResidueEquiv_closedPoint,Ideal.algebraMap_residueField_eq_zero]

theorem closedPoint_ker (p : Ideal A) [p.IsMaximal] :
    RingHom.ker (closedPoint p).toRingHom = p :=
  Ideal.ext (closedPoint_eq_zero_iff p)

/-- ℂ receives exactly the point action; the residue identification respects A. -/
abbrev closedPointAlgebra (p : Ideal A) [p.IsMaximal] : Algebra A ℂ :=
  (closedPoint p).toRingHom.toAlgebra

def residuePointEquiv (p : Ideal A) [p.IsMaximal] :
    let := closedPointAlgebra p
    p.ResidueField ≃ₐ[A] ℂ := by
  let := closedPointAlgebra p
  exact { (complexResidueEquiv p).symm.toRingEquiv with commutes' := fun _ => rfl }

end ClosedPoints
end KhanSL2.Factorization.ChartBridge
