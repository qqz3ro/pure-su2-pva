module

public import KhanSL2.Factorization.FiniteBGGTransferWindow
public import KhanSL2.Factorization.FiniteBGGComplex

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct
namespace KhanSL2.Factorization.BGGTransfer
open BGG BGGBridge SymmetricFamily PolynomialBGG Conditional
attribute [local instance] harmonicModule harmonicIsScalarTower harmonicSMulCommClass

/-- The actual window projection respects the original coefficient scalars. -/
theorem exteriorHarmonicProjQ_smul (B p : ℕ) (r : CoefficientRing B)
    (z : HarmonicQuotient (⋀[ℂ]^B BGG.Current)) :
    exteriorHarmonicProjQ B p (r • z) = r • exteriorHarmonicProjQ B p z := by
  apply Modules.polynomialCoordinates_intertwines (coefficientCoordinates B)
    (exteriorHarmonicProjQ B p) _ r z
  intro i z
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change (windowRelations B p).mkQ (exteriorHarmonicProj B p
      (harmonicScalarRaw (CoefficientRing B) (⋀[ℂ]^B BGG.Current)
        (coefficientCoordinates B (MvPolynomial.X i)) z)) =
      coefficientCoordinates B (MvPolynomial.X i) •
        (windowRelations B p).mkQ (exteriorHarmonicProj B p z)
    rw [← windowMkQ_smul,windowCoordinates_smul]
    congr 1
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,hz,hw]
    | tmul h n =>
      change PositiveCE.standardHarmonicProjection p h ⊗ₜ[ℂ]
        (coefficientCoordinates B (MvPolynomial.X i) • n) = _
      rw [exteriorCoefficientCoordinates_smul]
      rfl

def exteriorHarmonicWindowLinearEquiv (B p : ℕ) :
    harmonicDegree (CoefficientRing B) (⋀[ℂ]^B BGG.Current) p ≃ₗ[CoefficientRing B]
      WindowCoinvariants B p where
  __ := (exteriorHarmonicWindowEquiv B p).toAddEquiv
  map_smul' r z := exteriorHarmonicProjQ_smul B p r z.val

/-- The existing finite BGG terms, with their original coefficient actions,
are exactly the graded harmonic terms of the actual exterior coefficient complex. -/
def exteriorTermEquiv (B p : ℕ) :
    harmonicDegree (CoefficientRing B) (⋀[ℂ]^B BGG.Current) p ≃ₗ[CoefficientRing B]
      BGGComplex.Term B p :=
  (exteriorHarmonicWindowLinearEquiv B p).trans (termEquivWindowLinear B p).symm

/-- The coefficient inclusion in NB is the original current-module inclusion. -/
def exteriorCoefficientIncl (B : ℕ) : (⋀[ℂ]^B BGG.Current) →ₗ⁅ℂ,BGG.Current⁆ Current.NB :=
  (exteriorCurrentSubmodule B).incl

def exteriorGlobalMap (B : ℕ) :
    HarmonicQuotient (⋀[ℂ]^B BGG.Current) →ₗ[ℂ] HarmonicQuotient Current.NB :=
  harmonicMap (exteriorCoefficientIncl B).toLinearMap
    (constantEquivariant_of_lieHom (exteriorCoefficientIncl B))

theorem exteriorGlobalMap_inclQ (B p : ℕ) (z : WindowCoinvariants B p) :
    exteriorGlobalMap B (exteriorHarmonicInclQ B p z) = windowInclQ B p z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change (relH Current.NB).mkQ (harmonicRawMap (exteriorCoefficientIncl B).toLinearMap
      (exteriorHarmonicIncl B p z)) = (relH Current.NB).mkQ (windowIncl B p z)
    congr 1
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add,hz,hw]
    | tmul h n => rfl

theorem exteriorTermEquiv_toCoinvariants (B p : ℕ)
    (z : harmonicDegree (CoefficientRing B) (⋀[ℂ]^B BGG.Current) p) :
    BGGComplex.termToCoinvariants B p (exteriorTermEquiv B p z) = exteriorGlobalMap B z.val := by
  change BGGComplex.termToCoinvariants B p ((termEquivWindow B p).symm
    (exteriorHarmonicProjQ B p z.val)) = _
  rw [← windowInclQ_eq_termToCoinvariants,← exteriorGlobalMap_inclQ,
    exteriorHarmonicInclQ_projQ_of_mem]

theorem termToCoinvariants_differential (B p : ℕ) (z : BGGComplex.Term B (p+1)) :
    BGGComplex.termToCoinvariants B p (bggDifferential B p z) =
      dHq Current.NB (BGGComplex.termToCoinvariants B (p+1) z) := by
  have h : (BGGComplex.termToCoinvariants B p).comp (BGGComplex.differential B p) =
      (dHq Current.NB).comp (BGGComplex.termToCoinvariants B (p+1)) := by
    apply DirectSum.linearMap_ext
    intro S
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply,BGGComplex.differential_lof,BGGComplex.termToCoinvariants_lof]
    rfl
  exact LinearMap.congr_fun h z

/-- The equivalence preserves the specified transferred differential. -/
theorem exteriorTermEquiv_differential (B p : ℕ)
    (z : harmonicDegree (CoefficientRing B) (⋀[ℂ]^B BGG.Current) (p+1)) :
    exteriorTermEquiv B p (harmonicDegreeDifferential (CoefficientRing B) (⋀[ℂ]^B BGG.Current) p z) =
      bggDifferential B p (exteriorTermEquiv B (p+1) z) := by
  apply BGGComplex.termToCoinvariants_injective B p
  rw [exteriorTermEquiv_toCoinvariants,termToCoinvariants_differential,
    exteriorTermEquiv_toCoinvariants]
  exact harmonicMap_differential (exteriorCoefficientIncl B) z.val

end KhanSL2.Factorization.BGGTransfer
