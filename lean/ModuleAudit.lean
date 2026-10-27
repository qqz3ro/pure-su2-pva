module

import all KhanSL2.BasisGrading
import all KhanSL2.GradingDecomposition
import all KhanSL2.Basic
import all KhanSL2.CE
import all KhanSL2.Cocycles
import all KhanSL2.CEDerivationBasics
import all KhanSL2.CochainGrading
import all KhanSL2.CEDegrees
import all KhanSL2.CohomologyGrading
import all KhanSL2.ExteriorAlgebra
import all KhanSL2.ExteriorSigns
import all KhanSL2.ExteriorParity
import all KhanSL2.ExteriorRing
import all KhanSL2.ExteriorContraction
import all KhanSL2.Injectivity.FinitePairing
import all KhanSL2.Chains.Transpose
import all KhanSL2.CEExterior
import all KhanSL2.ExteriorSupercomm
import all KhanSL2.PVA
import all KhanSL2.CochainSupercomm
import all KhanSL2.ExteriorDerivation
import all KhanSL2.CELeibniz
import all KhanSL2.CESeries
import all KhanSL2.CESquareZero
import all KhanSL2.CEInvariantBasics
import all KhanSL2.CEEquivariance
import all KhanSL2.Chains.Coinvariant
import all KhanSL2.Chains.Dictionary
import all KhanSL2.Injectivity.ExteriorSubstitution
import all KhanSL2.Injectivity.CartanRestriction
import all KhanSL2.Injectivity.CartanContraction
import all KhanSL2.Injectivity.RootCurrent
import all KhanSL2.Injectivity.CurrentAdjoint
import all KhanSL2.Injectivity.ChainPairing
import all KhanSL2.Source
import all KhanSL2.SourceUniversal
import all KhanSL2.SourceSupercomm
import all KhanSL2.SourceParity
import all KhanSL2.SourceData
import all KhanSL2.LambdaPolynomialLemmas
import all KhanSL2.SourceJetActions
import all KhanSL2.SourceGeneratorChecks
import all KhanSL2.SourceHamiltonian
import all KhanSL2.LambdaPolynomialSkew
import all KhanSL2.SourceBracketOperators
import all KhanSL2.SourceBracketOperatorCalculus
import all KhanSL2.SourceParityProjections
import all KhanSL2.SourceBracket
import all KhanSL2.SourceGrading
import all KhanSL2.SourceHamiltonianDegree
import all KhanSL2.SourceHamiltonianLeibniz
import all KhanSL2.SourceAlgebra
import all KhanSL2.SourceSupercommUngraded
import all KhanSL2.SourceBracketOperatorParity
import all KhanSL2.SourceBracketLeibniz
import all KhanSL2.SourceHamiltonianExt
import all KhanSL2.SourceBracketQuotient
import all KhanSL2.SourceBracketParity
import all KhanSL2.SourceBracketSkew
import all KhanSL2.SourcePolynomialDegree
import all KhanSL2.SourceGeneration
import all KhanSL2.SourceBracketDegree
import all KhanSL2.SourceJacobiExtension
import all KhanSL2.SourceBracketGeneratorJacobi
import all KhanSL2.JacobiTranslation
import all KhanSL2.SourceJacobiThird
import all KhanSL2.JacobiPermutation
import all KhanSL2.JacobiLastPermutation
import all KhanSL2.SourceBracketJacobi
import all KhanSL2.SourcePVA
import all KhanSL2.PVAMap
import all KhanSL2.SourceMapBracket
import all KhanSL2.CEConvolutionArithmetic
import all KhanSL2.CETranslationGenerator
import all KhanSL2.CETranslation
import all KhanSL2.Data
import all KhanSL2.CEComplex
import all KhanSL2.BCModeKernel
import all KhanSL2.BCFullCE
import all KhanSL2.BCFullKernel
import all KhanSL2.BCFullBracketDefinition
import all KhanSL2.BCSkewCalculus
import all KhanSL2.BCFullBracketSkew
import all KhanSL2.BCFullGrading
import all KhanSL2.BCFullAlgebra
import all KhanSL2.BCFullBracketDegree
import all KhanSL2.BCFullBracketLaws
import all KhanSL2.BCFullGeneration
import all KhanSL2.BCFullBracketSesqui
import all KhanSL2.BCFullJacobi
import all KhanSL2.BCFullPVA
import all KhanSL2.ExteriorReindex
import all KhanSL2.BCFullEmbedding
import all KhanSL2.BCFullDifferential
import all KhanSL2.BCFullTranslation
import all KhanSL2.BCHamiltonianCalculus
import all KhanSL2.BCFullHamiltonian
import all KhanSL2.BCFullHamiltonianB0
import all KhanSL2.BCFullHamiltonianIdentity
import all KhanSL2.BCBracketDefinition
import all KhanSL2.BCFullBracketEmbedding
import all KhanSL2.BCBracketSkew
import all KhanSL2.BCBracketDegree
import all KhanSL2.BCBracketLaws
import all KhanSL2.CochainGeneration
import all KhanSL2.BCBracketSesqui
import all KhanSL2.CochainJacobi
import all KhanSL2.CochainAlgebra
import all KhanSL2.BCPVA
import all KhanSL2.CochainBracketDerivation
import all KhanSL2.BCColor
import all KhanSL2.PVATransport
import all KhanSL2.PVASubquotient
import all KhanSL2.CohomologyDescent
import all KhanSL2.RelativeHamiltonian
import all KhanSL2.TargetPVA
import all KhanSL2.CanonicalTarget
import all KhanSL2.CanonicalPrimitives
import all KhanSL2.CanonicalInvariants
import all KhanSL2.CanonicalRelations
import all KhanSL2.CanonicalMixed
import all KhanSL2.CanonicalBoundaryDescent
import all KhanSL2.CanonicalBracket
import all KhanSL2.CanonicalVanish
import all KhanSL2.CanonicalMap
import all KhanSL2.Injectivity.CartanFunctional
import all KhanSL2.Injectivity.ClosedCurrentFamilies
import all KhanSL2.Injectivity.OrderedProducts
import all KhanSL2.Injectivity.NewtonCycles
import all KhanSL2.Injectivity.NewtonPolynomials
import all KhanSL2.Injectivity.RootCycles
import all KhanSL2.Injectivity.RootPolynomialEncoding
import all KhanSL2.Injectivity.FiniteSupport
import all KhanSL2.Injectivity.CartanSupport
import all KhanSL2.Injectivity.RootEncodingSupport
import all KhanSL2.Injectivity.RootClosedFamilies
import all KhanSL2.Injectivity.ExteriorWords
import all KhanSL2.Injectivity.ExteriorPolynomialEvaluation
import all KhanSL2.Injectivity.CartanPolynomialEvaluation
import all KhanSL2.Injectivity.CartanBlockDeterminant
import all KhanSL2.Injectivity.RootAlternation
import all KhanSL2.Injectivity.CartanTensor
import all KhanSL2.Injectivity.RootCyclePairing
import all KhanSL2.Injectivity.CartanTensorEvaluation
import all KhanSL2.Injectivity.DiagonalDivisibility
import all KhanSL2.Injectivity.DiagonalFactors
import all KhanSL2.Injectivity.VandermondeFactors
import all KhanSL2.Injectivity.VandermondeAppend
import all KhanSL2.Injectivity.BlockSymmetry
import all KhanSL2.Injectivity.SchurAlternants
import all KhanSL2.Injectivity.AlternantProductSpan
import all KhanSL2.Injectivity.CyclePolynomialIdentities
import all KhanSL2.Injectivity.CycleNormalization
import all KhanSL2.Injectivity.SelectedCycles
import all KhanSL2.Injectivity.SourceSectors
import all KhanSL2.Injectivity.SourceWordPairing
import all KhanSL2.Injectivity.CartanJets
import all KhanSL2.Injectivity.ExteriorDeterminant
import all KhanSL2.Injectivity.ExteriorSeries
import all KhanSL2.Injectivity.AxisSeries
import all KhanSL2.Injectivity.CartanSeriesSlots
import all KhanSL2.Injectivity.CartanSeriesWord
import all KhanSL2.Injectivity.TaylorPolynomial
import all KhanSL2.Injectivity.TaylorCoefficients
import all KhanSL2.Injectivity.TaylorChainComparison
import all KhanSL2.Injectivity.DiagonalCoefficients
import all KhanSL2.Injectivity.TaylorRelations
import all KhanSL2.Injectivity.TaylorJetConvolution
import all KhanSL2.Injectivity.TaylorHeadRelations
import all KhanSL2.Injectivity.TaylorMixedRelations
import all KhanSL2.Injectivity.TaylorOddRelations
import all KhanSL2.Injectivity.MonomialSymmetry
import all KhanSL2.Injectivity.TaylorSymmetry
import all KhanSL2.Injectivity.TaylorVanishing
import all KhanSL2.Injectivity.DiagonalCovariance
import all KhanSL2.Injectivity.TaylorDiagonals
import all KhanSL2.Injectivity.TaylorDiscriminant
import all KhanSL2.Injectivity.SourcePolynomialSpan
import all KhanSL2.Injectivity.TaylorLinear
import all KhanSL2.Injectivity.TaylorRealization
import all KhanSL2.Injectivity.TaylorSeparation
import all KhanSL2.Injectivity.SectorLinearSeparation
import all KhanSL2.Injectivity.GradedSeparation
import all KhanSL2.Injectivity
import all KhanSL2.Chains.Psi
import all KhanSL2.CurrentAlgebra
import all KhanSL2.ColorBasis
import all KhanSL2.Chains.CurrentModel
import all KhanSL2.LieChains.DerivExt
import all KhanSL2.LieChains.Basic
import all KhanSL2.Chains.Comparison.Setup
import all KhanSL2.Chains.Comparison.Transfer
import all KhanSL2.Chains.Comparison.Generators
import all KhanSL2.Chains.Comparison.Support
import all KhanSL2.Chains.Comparison.Intertwine
import all KhanSL2.Chains.Comparison.Boundary
import all KhanSL2.Chains.Comparison.Bijective
import all KhanSL2.Chains.RelativeHomology
import all KhanSL2.LieChains.Grading
import all KhanSL2.Chains.Grading
import all KhanSL2.Chains.RelativeComplex
import all KhanSL2.DictionaryStatement
import all KhanSL2.Modules.GradedAssembly
import all KhanSL2.Modules.PolynomialModels
import all KhanSL2.Modules.PolynomialComparison
import all KhanSL2.Modules.WeightedRoots
import all KhanSL2.Modules.PolynomialSectors
import all KhanSL2.Modules.PolynomialMap
import all KhanSL2.Modules.SourceDualPieces
import all KhanSL2.Modules.SourceDualTaylor
import all KhanSL2.Modules.SourceDualAssembly
import all KhanSL2.Modules.SourceDualModel
import all KhanSL2.Modules.SourceDualShift
import all KhanSL2.Modules.CoefficientOperators
import all KhanSL2.Modules.CoefficientHomology
import all KhanSL2.Modules.PowerSumCoordinates
import all KhanSL2.Modules.CoefficientAction
import all KhanSL2.Modules.ModeShifts
import all KhanSL2.Modules.CoefficientComparison
import all KhanSL2.Modules.CoefficientPairing
import all KhanSL2.Modules.ModeShiftAdjoint
import all KhanSL2.Modules.ShiftJets
import all KhanSL2.Modules.ShiftWords
import all KhanSL2.Modules.CoefficientJetPairing
import all KhanSL2.Modules.CoefficientLinearity
import all KhanSL2.Depth.GraphRegular
import all KhanSL2.Depth.Collision
import all KhanSL2.Depth.MonicCoeffs
import all KhanSL2.Depth.Toolkit
import all KhanSL2.Depth.FiniteMap
import all KhanSL2.Depth.SourceCoords
import all KhanSL2.Depth.TwoBlock
import all KhanSL2.Depth.SourceModules
import all KhanSL2.Modules.DepthPolynomialComparison
import all KhanSL2.Modules.DepthModuleComparison
import all KhanSL2.BGGBridge.BaseChange
import all KhanSL2.BGG.Current
import all KhanSL2.BGG.CurrentCoordinates
import all KhanSL2.BGG.CurrentPositive
import all KhanSL2.BGG.CurrentBasis
import all KhanSL2.BGG.ExteriorModel
import all KhanSL2.BGG.PositiveCE
import all KhanSL2.BGG.PositiveBoundary
import all KhanSL2.BGG.FreeCEBasis
import all KhanSL2.BGG.CurrentScaling
import all KhanSL2.BGG.WordGrading
import all KhanSL2.BGG.Augmentation
import all KhanSL2.BGG.UEGeneration
import all KhanSL2.BGG.EnvelopingGrading
import all KhanSL2.BGG.Induced
import all KhanSL2.BGG.FreeCE
import all KhanSL2.BGG.Vacuum
import all KhanSL2.BGG.FirstMaps
import all KhanSL2.BGG.CurrentUEGrading
import all KhanSL2.BGG.CurrentPBW
import all KhanSL2.BGG.InducedScalarLift
import all KhanSL2.BGG.InducedFactorization
import all KhanSL2.BGG.RelativeProjectivity
import all KhanSL2.BGG.Terms
import all KhanSL2.BGG.InducedBaseMap
import all KhanSL2.BGG.TermGrading
import all KhanSL2.BGG.TermPBW
import all KhanSL2.BGG.TermPBWAction
import all KhanSL2.BGG.PositiveBoundaryAdjoint
import all KhanSL2.BGG.RootEnergy
import all KhanSL2.BGG.RootExterior
import all KhanSL2.BGG.RootExteriorCurrent
import all KhanSL2.BGG.ExteriorAction
import all KhanSL2.BGG.RootAction
import all KhanSL2.BGG.RootExteriorPieces
import all KhanSL2.BGG.RootActionEnergy
import all KhanSL2.BGG.RootCartan
import all KhanSL2.BGG.RootHighest
import all KhanSL2.BGG.ColorRoot
import all KhanSL2.BGG.ColorRootEquivariance
import all KhanSL2.BGG.PositiveCEParity
import all KhanSL2.BGG.PositiveBoundaryEquivariance
import all KhanSL2.BGG.FreeCEEquivarianceAction
import all KhanSL2.BGGBridge.Coefficients
import all KhanSL2.BGGBridge.ContractionOps
import all KhanSL2.BGG.PositiveLaplacianBasics
import all KhanSL2.BGG.ExteriorSecondOrder
import all KhanSL2.BGG.ExteriorSecondOrderCalculus
import all KhanSL2.BGG.PositiveLaplacianOrder
import all KhanSL2.BGG.PositiveBoundaryProducts
import all KhanSL2.BGG.PositiveLaplacianPairs
import all KhanSL2.BGG.ExteriorEuler
import all KhanSL2.BGG.ColorRootGrading
import all KhanSL2.BGG.PositiveEnergyCasimir
import all KhanSL2.BGG.PositiveLaplacian
import all KhanSL2.BGG.RootCasimir
import all KhanSL2.BGG.ColorCasimir
import all KhanSL2.BGG.RootCasimirKernel
import all KhanSL2.BGG.PositiveSpectralKernel
import all KhanSL2.BGG.PositiveCEGrading
import all KhanSL2.BGG.GradedKernel
import all KhanSL2.BGG.PositiveHarmonics
import all KhanSL2.BGG.CasimirSplitting
import all KhanSL2.BGG.GradedSpectralSplitting
import all KhanSL2.BGG.GreenOperator
import all KhanSL2.BGG.HodgeContraction
import all KhanSL2.BGG.PositiveContraction
import all KhanSL2.BGG.PositiveContractionGrading
import all KhanSL2.BGG.PositiveHarmonicPieces
import all KhanSL2.BGG.PositiveHarmonicDecomposition
import all KhanSL2.BGG.EquivariantHarmonicDecomposition
import all KhanSL2.BGG.ContractionBaseChange
import all KhanSL2.BGG.PositiveTransferBase
import all KhanSL2.BGG.FiltrationNilpotence
import all KhanSL2.BGG.PositiveTransferFiltration
import all KhanSL2.BGG.FreeCEAugmentation
import all KhanSL2.BGG.PolynomialKoszul
import all KhanSL2.BGG.FreeCEOperators
import all KhanSL2.BGG.FreeCEFiniteSquare
import all KhanSL2.BGG.FreeCESupport
import all KhanSL2.BGG.FreeCESquareZero
import all KhanSL2.BGG.PositiveTransfer
import all KhanSL2.BGG.TermPBWGrading
import all KhanSL2.BGG.TermPBWFree
import all KhanSL2.BGG.HarmonicTensorTerms
import all KhanSL2.BGG.PositiveTransferDegreeBase
import all KhanSL2.BGG.PositiveTransferDegree
import all KhanSL2.BGG.FreeCEEquivarianceContraction
import all KhanSL2.BGG.FreeCEEquivariance
import all KhanSL2.BGG.PerturbationEquivariance
import all KhanSL2.BGG.PositiveTransferEquivariance
import all KhanSL2.BGG.PositiveEnergyScale
import all KhanSL2.BGG.FreeCEEnergy
import all KhanSL2.BGG.PositiveTransferEnergy
import all KhanSL2.BGGBridge.Transfer
import all KhanSL2.BGGBridge.ExteriorIso
import all KhanSL2.BGGBridge.BoundaryCompare
import all KhanSL2.BGGBridge.ChainIso
import all KhanSL2.BGGBridge.GradingOps
import all KhanSL2.BGG.ContractionHomology
import all KhanSL2.BGG.ContractionDegreeHomology
import all KhanSL2.BGGBridge.Windows
import all KhanSL2.BGG.FreeCEAugmentationEquivariance
import all KhanSL2.BGGBridge.TrivialCoefficients
import all KhanSL2.BGGBridgeStatement
import all KhanSL2.Modules.BGGAssembly
import all KhanSL2.Modules

public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

open Lean Elab Command

elab "#audit_concrete_modules" : command => do
  let env ← getEnv
  let isModule := fun (m : Name) => (`KhanSL2.Modules).isPrefixOf m
  let names := env.constants.toList.filterMap fun (name, info) =>
    let fromModule := match env.getModuleIdxFor? name with
      | some idx => isModule env.header.moduleNames[idx.toNat]!
      | none => false
    if fromModule && !info.isUnsafe then some name else none
  for required in #[`KhanSL2.Modules.R, `KhanSL2.Modules.JB,
      `KhanSL2.Modules.nu, `KhanSL2.Modules.KTotal,
      `KhanSL2.Modules.psiB, `KhanSL2.Modules.kTotalEquivBGG,
      `KhanSL2.Modules.sourceDualEquiv, `KhanSL2.Modules.coefficientAction,
      `KhanSL2.Modules.psiBLinear, `KhanSL2.Modules.depthJBEquiv] do
    unless names.contains required do
      throwError "Missing concrete definition: {required}"
  for name in names do
    for ax in (← collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Forbidden axiom in {name}: {ax}"
  logInfo m!"PASS: {names.length} safe concrete-module declarations; no sorryAx or additional axioms."

noncomputable section

open KhanSL2 KhanSL2.Modules

example (B : ℕ) : R B = ↥(MvPolynomial.symmetricSubalgebra (Fin B) ℂ) := rfl
example (B p : ℕ) : KTotal B p = DirectSum ℤ (fun spin => Current.K p B spin) := rfl
example (r s : ℕ) : J r s = ↥(JSubmodule r s) := rfl
example (B : ℕ) : CommRing (R B) := inferInstance
example (B p : ℕ) : Module (R B) (JB B p) := inferInstance
example (r s : ℕ) : R (r + 3 * s) →ₐ[ℂ] S r s := nu r s
example (B p : ℕ) : KTotal B p →ₗ[ℂ] JB B p := psiB B p
#check (psiTotal_surjective : ∀ B p : ℕ, Function.Surjective (psiTotal B p))
#check (kTotalEquivBGG : ∀ B p : ℕ, KTotal B p ≃ₗ[ℂ] BGGHomologyTotal B p)
#check (sourceFunctional_restrict : ∀ (p B : ℕ) (spin : ℤ)
  (k : Current.K p B spin) (a : Source.piece (Current.kDegree p B spin)),
  sourceFunctional p B spin k a = Current.psiK p B spin k a)
#check (validSector_iff : ∀ B p : ℕ, ValidSector B p ↔ ∃ s : ℕ, B = p + 3 * s)
#check (jb_eq_zero_of_invalid : ∀ {B p : ℕ}, ¬ValidSector B p → ∀ q : JB B p, q = 0)
#check (nu_powerSum : ∀ r s m : ℕ,
  (nu r s (powerSum (r + 3 * s) m) : Polynomial r s) =
    MvPolynomial.rename Sum.inl (MvPolynomial.psum (Fin r) ℂ m) +
      (3 : Polynomial r s) * MvPolynomial.rename Sum.inr (MvPolynomial.psum (Fin s) ℂ m))
#check (psiB_of_valid : ∀ (B p : ℕ) (h : ValidSector B p) (x : KTotal B p),
  psiB B p x = jToJB B p h (psiPolynomial p (sectorS B p) (kTotalCast h p x)))
#check psiPolynomialSector_coeff_psiK
#check (psiPolynomialSector_homogeneous : ∀ (r s N : ℕ)
  (k : Current.K r (r + 3 * s) (sectorSpinBase r s + N)),
  (psiPolynomialSector r s N k : Polynomial r s).IsHomogeneous N)
#audit_concrete_modules
#print axioms KhanSL2.Modules.psiTotal_surjective
#print axioms KhanSL2.Modules.psiB
#print axioms KhanSL2.Modules.kTotalEquivBGG

-- These checks pin actual objects and prohibit replacement by assumed models.
example (B p : ℕ) : Module (R B) (KTotal B p) := inferInstance
#check (sourceDualEquiv : ∀ B p : ℕ, sourceDualTotal B p ≃ₗ[ℂ] JB B p)
#check (coefficientAction : ∀ B p : ℕ, R B →ₐ[ℂ] Module.End ℂ (KTotal B p))
#check (psiBLinear : ∀ B p : ℕ, KTotal B p →ₗ[R B] JB B p)
example (B p : ℕ) (x : KTotal B p) : psiBLinear B p x = psiB B p x := rfl
#check (psiBLinear_surjective : ∀ B p : ℕ, Function.Surjective (psiBLinear B p))
#check psiBLinear_restrictScalars
#check psiB_eq_sourceDualEquiv_comp_psiTotal
#check psiB_coefficientTotalPower
#check depthJBEquiv
#print axioms KhanSL2.Modules.sourceDualEquiv
#print axioms KhanSL2.Modules.coefficientAction
#print axioms KhanSL2.Modules.psiBLinear_surjective
#print axioms KhanSL2.Modules.depthJBEquiv
