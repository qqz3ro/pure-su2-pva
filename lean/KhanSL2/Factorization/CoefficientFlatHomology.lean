module

public import KhanSL2.Factorization.ShortQuotientCongr
public import KhanSL2.Factorization.ScalarPairHomology
public import KhanSL2.Factorization.RelativeChainsScalarComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily
variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]
attribute [local instance] coefficientChainModule coefficientChainIsScalarTower
  coefficientChainSMulCommClass coefficientTotalHomologyModule
  coefficientTotalHomologyIsScalarTower coefficientTotalHomologySMulCommClass

theorem coefficientChainAction_differential (r : R) :
    (coefficientChainAction R M r).comp (differential M) =
      (differential M).comp (coefficientChainAction R M r) := by
  apply LinearMap.ext
  exact coefficientMap_differential (coefficientScalarLieHom R M r)

/-- The same total CE differential, as a coefficient-linear short complex. -/
abbrev coefficientTotalShortComplex : ShortComplex (ModuleCat R) :=
  scalarPairShortComplex R (differential M) (differential_comp_self M)
    (coefficientChainAction R M) (coefficientChainAction_differential R M)

/-- Its explicit quotient is precisely the original total homology with its original action. -/
def coefficientTotalQuotientEquiv :
    (coefficientTotalShortComplex R M).moduleCatLeftHomologyData.H ≃ₗ[R] TotalHomology M :=
  LinearEquiv.ofBijective
    (scalarPairQuotientMap R (differential M) (differential_comp_self M)
      (coefficientChainAction R M) (coefficientChainAction_differential R M))
    (scalarPairQuotientMap_bijective R (differential M) (differential_comp_self M)
      (coefficientChainAction R M) (coefficientChainAction_differential R M))

@[simp] theorem coefficientTotalQuotientEquiv_mk
    (z : LinearMap.ker (coefficientTotalShortComplex R M).g.hom) :
    coefficientTotalQuotientEquiv R M (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (⟨z.val,z.property⟩ : LinearMap.ker (differential M)) := rfl

@[simp] theorem coefficientTotalQuotientEquiv_symm_mk
    (z : LinearMap.ker (differential M)) :
    (coefficientTotalQuotientEquiv R M).symm (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (⟨z.val,z.property⟩ : LinearMap.ker (coefficientTotalShortComplex R M).g.hom) := by
  apply (coefficientTotalQuotientEquiv R M).injective
  rw [LinearEquiv.apply_symm_apply]
  rfl

variable (A : Type) [CommRing A] [Algebra R A] [Algebra ℂ A] [IsScalarTower ℂ R A]

/-- The scalar-extended total short complex has the same actual coefficient-chain quotient. -/
def coefficientScalarQuotientEquiv :
    ((coefficientTotalShortComplex R M).map (scalarFunctor A)).moduleCatLeftHomologyData.H ≃ₗ[A]
      (coefficientTotalShortComplex A (CoefficientBaseChange R M A)).moduleCatLeftHomologyData.H :=
  shortQuotientCongr _ _ (relativeChainsScalarEquiv R M A)
    (relativeChainsScalarEquiv R M A) (relativeChainsScalarEquiv R M A)
    (relativeChainsScalarMap_differential R M A) (relativeChainsScalarMap_differential R M A)

/-- Flat base change on actual total relative homology. The coefficient action
is the original one, and the equivalence is the canonical represented-cycle map. -/
def coefficientFlatHomologyEquiv [Module.Flat R A] :
    A ⊗[R] TotalHomology M ≃ₗ[A] TotalHomology (CoefficientBaseChange R M A) :=
  ((coefficientTotalQuotientEquiv R M).symm.baseChange R A _ _).trans
    ((flatShortQuotientEquiv A (coefficientTotalShortComplex R M)).trans
      ((coefficientScalarQuotientEquiv R M A).trans
        (coefficientTotalQuotientEquiv A (CoefficientBaseChange R M A))))

/-- On unit tensors this canonical equivalence is exactly the map induced by
inserting the coefficient into its original scalar extension. -/
theorem coefficientFlatHomologyEquiv_unit [Module.Flat R A] (h : TotalHomology M) :
    coefficientFlatHomologyEquiv R M A (1 ⊗ₜ[R] h) =
      coefficientTotalHomologyMap (coefficientBaseChangeUnit R M A) h := by
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (PerfectDuality.pairBoundaries (differential M) (differential M)) h
  change coefficientTotalQuotientEquiv A (CoefficientBaseChange R M A)
    (coefficientScalarQuotientEquiv R M A
      (flatShortQuotientEquiv A (coefficientTotalShortComplex R M)
        (1 ⊗ₜ[R] (coefficientTotalQuotientEquiv R M).symm (Submodule.Quotient.mk z)))) = _
  rw [coefficientTotalQuotientEquiv_symm_mk,flatShortQuotientEquiv_mk]
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  change relativeChainsScalarMap R M A
    (flatShortCyclesEquiv A (coefficientTotalShortComplex R M)
      (1 ⊗ₜ[R] (⟨z.val,z.property⟩ : LinearMap.ker (coefficientTotalShortComplex R M).g.hom))).val = _
  rw [flatShortCyclesEquiv_val,LinearMap.baseChange_tmul]
  change (1:A) • coefficientMap (coefficientBaseChangeUnit R M A).toLinearMap
    (constantEquivariant_of_lieHom (coefficientBaseChangeUnit R M A)) z.val = _
  rw [one_smul]
  rfl

end KhanSL2.Factorization
