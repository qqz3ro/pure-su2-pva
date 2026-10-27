module

import all KhanSL2.Basic
import all KhanSL2.CE
import all KhanSL2.Cocycles
import all KhanSL2.CEDerivationBasics
import all KhanSL2.BasisGrading
import all KhanSL2.CochainGrading
import all KhanSL2.CEDegrees
import all KhanSL2.ExteriorAlgebra
import all KhanSL2.ExteriorSigns
import all KhanSL2.ExteriorParity
import all KhanSL2.ExteriorRing
import all KhanSL2.CEExterior
import all KhanSL2.ExteriorSupercomm
import all KhanSL2.PVA
import all KhanSL2.CochainSupercomm
import all KhanSL2.ExteriorContraction
import all KhanSL2.ExteriorDerivation
import all KhanSL2.CELeibniz
import all KhanSL2.CESeries
import all KhanSL2.CESquareZero
import all KhanSL2.CEInvariantBasics
import all KhanSL2.CEEquivariance
import all KhanSL2.Deformation.Derivations
import all KhanSL2.CEConvolutionArithmetic
import all KhanSL2.CETranslationGenerator
import all KhanSL2.CETranslation
import all KhanSL2.Deformation.Delta
import all KhanSL2.CurrentAlgebra
import all KhanSL2.BGG.Current
import all KhanSL2.BGG.CurrentCoordinates
import all KhanSL2.BGG.CurrentPositive
import all KhanSL2.BGG.CurrentBasis
import all KhanSL2.BGG.RootEnergy
import all KhanSL2.BGG.RootExterior
import all KhanSL2.BGG.RootExteriorCurrent
import all KhanSL2.Injectivity.ExteriorSubstitution
import all KhanSL2.BGG.ExteriorModel
import all KhanSL2.BGG.ExteriorAction
import all KhanSL2.BGG.RootAction
import all KhanSL2.BGG.RootExteriorPieces
import all KhanSL2.BGG.RootActionEnergy
import all KhanSL2.BGG.RootCartan
import all KhanSL2.BGG.RootHighest
import all KhanSL2.BGG.RootCasimir
import all KhanSL2.BGG.PositiveCE
import all KhanSL2.ColorBasis
import all KhanSL2.BGG.ColorRoot
import all KhanSL2.BGG.ColorRootEquivariance
import all KhanSL2.BGG.ExteriorEuler
import all KhanSL2.BGG.ColorRootGrading
import all KhanSL2.BGG.PositiveCEParity
import all KhanSL2.BGG.ExteriorSecondOrder
import all KhanSL2.BGG.ExteriorSecondOrderCalculus
import all KhanSL2.BGG.PositiveEnergyCasimir
import all KhanSL2.BGG.ColorCasimir
import all KhanSL2.BGG.CasimirSplitting
import all KhanSL2.Injectivity.FinitePairing
import all KhanSL2.Injectivity.FiniteSupport
import all KhanSL2.BGG.PositiveBoundary
import all KhanSL2.BGG.FreeCEBasis
import all KhanSL2.Deformation.Sl2Casimir
import all KhanSL2.Deformation.RestrictedActions
import all KhanSL2.Deformation.SplitOps
import all KhanSL2.ExteriorReindex
import all KhanSL2.Deformation.RelabelOne
import all KhanSL2.Deformation.SplitDifferential
import all KhanSL2.Deformation.PureModes
import all KhanSL2.Deformation.SplitIdentities
import all KhanSL2.Deformation.Grading
import all KhanSL2.Deformation.SplitGradings
import all KhanSL2.Deformation.BDecomposition
import all KhanSL2.Deformation.CasimirReduction
import all KhanSL2.Deformation.Staircase
import all KhanSL2.BGGBridge.BaseChange
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
import all KhanSL2.BGG.PositiveBoundaryEquivariance
import all KhanSL2.BGG.FreeCEEquivarianceAction
import all KhanSL2.BGGBridge.Coefficients
import all KhanSL2.BGGBridge.ContractionOps
import all KhanSL2.BGG.PositiveLaplacianBasics
import all KhanSL2.BGG.PositiveLaplacianOrder
import all KhanSL2.BGG.PositiveBoundaryProducts
import all KhanSL2.BGG.PositiveLaplacianPairs
import all KhanSL2.BGG.PositiveLaplacian
import all KhanSL2.BGG.RootCasimirKernel
import all KhanSL2.BGG.PositiveSpectralKernel
import all KhanSL2.BGG.PositiveCEGrading
import all KhanSL2.BGG.GradedKernel
import all KhanSL2.BGG.PositiveHarmonics
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
import all KhanSL2.GradingDecomposition
import all KhanSL2.CohomologyGrading
import all KhanSL2.Chains.Transpose
import all KhanSL2.Chains.Coinvariant
import all KhanSL2.Chains.Dictionary
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
import all KhanSL2.BGGBridge.ExteriorIso
import all KhanSL2.BGGBridge.BoundaryCompare
import all KhanSL2.BGGBridge.ChainIso
import all KhanSL2.BGGBridge.GradingOps
import all KhanSL2.DictionaryStatement
import all KhanSL2.BGG.ContractionHomology
import all KhanSL2.BGG.ContractionDegreeHomology
import all KhanSL2.BGGBridge.Windows
import all KhanSL2.BGG.FreeCEAugmentationEquivariance
import all KhanSL2.BGGBridge.TrivialCoefficients
import all KhanSL2.Deformation.AcyclicOne
import all KhanSL2.Deformation.Kunneth
import all KhanSL2.Deformation.SplitExact
import all KhanSL2.Deformation.SplitMap
import all KhanSL2.Deformation.CohomologyOps
import all KhanSL2.Deformation.GeneratorImages
import all KhanSL2.Deformation.PhiDelta
import all KhanSL2.Deformation.SourceContraction
import all KhanSL2.Deformation.SourceHomotopy
import all KhanSL2.Deformation.LowDegreeStaircase
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
import all KhanSL2.Depth.Descent
import all KhanSL2.Depth.SourceDepth
import all KhanSL2.Depth.SourceDescent
import all KhanSL2.Conditional.Coefficients
import all KhanSL2.Deformation.LowDegree
import all KhanSL2.BGGBridgeStatement
import all KhanSL2.Modules.BGGAssembly
import all KhanSL2.BGGBridge.CoefficientWeights
import all KhanSL2.BGGBridge.CoefficientProjection
import all KhanSL2.BGGBridge.TensorCoinvariants
import all KhanSL2.BGGBridge.TermVanishing
import all KhanSL2.Conditional.BGGComplex
import all KhanSL2.BGGBridge.CoefficientOps
import all KhanSL2.BGGBridge.CoefficientWindows
import all KhanSL2.Conditional.BGGPower
import all KhanSL2.Conditional.BGGHomology
import all KhanSL2.Conditional.BGGAction
import all KhanSL2.BGG.HarmonicEnergy
import all KhanSL2.Conditional.TopEmbedding
import all KhanSL2.BGGBridge.TopAlternantsMap
import all KhanSL2.BGGBridge.TopLadder
import all KhanSL2.BGGBridge.TopWeights
import all KhanSL2.BGGBridge.TopSpanning
import all KhanSL2.BGGBridge.TopGeneratorWindow
import all KhanSL2.BGGBridge.TopPolynomialMap
import all KhanSL2.BGGBridge.TopAlternants
import all KhanSL2.BGGBridge.TopWeightBasis
import all KhanSL2.Conditional.TopCyclicity
import all KhanSL2.Conditional.Top
import all KhanSL2.Conditional.TopCyclicAlgebra
import all KhanSL2.Conditional.BGGCycleAction
import all KhanSL2.BGGBridge.CoefficientComparison
import all KhanSL2.Conditional.BGGHomologyAction
import all KhanSL2.Conditional.BGGComparison
import all KhanSL2.Conditional.TopComparison
import all KhanSL2.Conditional.TopRankOne
import all KhanSL2.PolynomialBGG.RootRing
import all KhanSL2.PolynomialBGG.ColoredWords
import all KhanSL2.PolynomialBGG.ColoredClasses
import all KhanSL2.PolynomialBGG.HarmonicSpanning
import all KhanSL2.PolynomialBGG.FiniteTerms
import all KhanSL2.PolynomialBGG.RootRingStep
import all KhanSL2.PolynomialBGG.RootRingCoordinates
import all KhanSL2.PolynomialBGG.RootRingBaseChange
import all KhanSL2.PolynomialBGG.RootRingFree
import all KhanSL2.PolynomialBGG.ProjectiveModel
import all KhanSL2.PolynomialBGG.ProjectiveModelDeriv
import all KhanSL2.PolynomialBGG.ProjectiveModelExterior
import all KhanSL2.PolynomialBGG.ProjectiveModelRetract
import all KhanSL2.PolynomialBGG.ColoredWindows
import all KhanSL2.PolynomialBGG.ProjectiveModelWindow
import all KhanSL2.PolynomialBGG.ProjectiveModelAction
import all KhanSL2.PolynomialBGG.ProjectiveModelLabelled
import all KhanSL2.PolynomialBGG.TensorModel
import all KhanSL2.PolynomialBGG.TensorColors
import all KhanSL2.PolynomialBGG.TensorAction
import all KhanSL2.PolynomialBGG.ProjectiveModelLinear
import all KhanSL2.PolynomialBGG.ProjectiveModelColors
import all KhanSL2.PolynomialBGG.LabelledRoot
import all KhanSL2.PolynomialBGG.ProjectiveTerms
import all KhanSL2.Conditional.BGGInput
import all KhanSL2.Conditional.DepthAssembly
import all KhanSL2.Conditional.KernelTransport
import all KhanSL2.PVAIsomorphism
import all KhanSL2.MainStatement
import all KhanSL2.InjectivityMainStatement
import all KhanSL2.Conditional.Duality
import all KhanSL2.Conditional.Assembly
import all KhanSL2.Deformation.Assembly
import all KhanSL2.Deformation
import all Deformation

public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

/-! Audit of the deformation step (paper §5, Prop. 5.3).

Every project module in the import closure is imported with `import all`, so private proof
bodies are visible to the axiom collector. The audit checks that the key results are proved
theorems and that no declaration of the deformation development uses an axiom beyond
`propext`, `Classical.choice` and `Quot.sound`. -/

open Lean Elab Command

elab "#audit_deformation" : command => do
  let env ← getEnv
  for removed in #[`KhanSL2.Conditional.RemainingInputs.lowDegrees,
      `KhanSL2.Conditional.RemainingInputs.polynomialBGG,
      `KhanSL2.Conditional.BGGPolynomialProperties.finite,
      `KhanSL2.Conditional.BGGPolynomialProperties.top,
      `KhanSL2.Conditional.BGGPolynomialProperties.above,
      `KhanSL2.Conditional.BGGScalarStructure,
      `KhanSL2.Conditional.BGGPolynomialProperties.compatibleScalars,
      `KhanSL2.Conditional.BGGPolynomialProperties.comparison_smul] do
    if (env.find? removed).isSome then
      throwError "A discharged hypothesis has been restored: {removed}"
  let isProjectModule := fun (name : Name) => (`KhanSL2).isPrefixOf name || name == `Deformation
  for imported in env.header.modules do
    if isProjectModule imported.module && !imported.importAll then
      throwError "Missing proof bodies in {imported.module}"
  for n in #[`KhanSL2.lowDegreeStep,
      `KhanSL2.Conditional.mainStatement_of_twoInputs,
      `KhanSL2.Conditional.psiB_bijective_of_twoInputs,
      `KhanSL2.Conditional.remainingInputs_iff_two,
      `KhanSL2.surj_zero, `KhanSL2.surj_one, `KhanSL2.psi_injective_iff_surj,
      `KhanSL2.totalZero_exact, `KhanSL2.totalOne_exact,
      `KhanSL2.splitMap_D0, `KhanSL2.dpp_exact, `KhanSL2.kunneth, `KhanSL2.dC_exact_fine,
      `KhanSL2.Source.phi_deltaBar_exact, `KhanSL2.Source.anticomm_energy,
      `KhanSL2.Deformation.Staircase.bottom, `KhanSL2.Deformation.Staircase.shift_injective,
      `KhanSL2.Deformation.Staircase.shift_surjective, `KhanSL2.Deformation.Staircase.assembly,
      `KhanSL2.Deformation.CasimirHomotopy.casimir_reduction,
      `KhanSL2.Deformation.casimir_ker, `KhanSL2.Deformation.casimir_isCompl] do
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected proved theorem {n}"
  let names := env.constants.toList.filterMap fun (n, info) =>
    let included := match env.getModuleIdxFor? n with
      | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        (`KhanSL2.Deformation).isPrefixOf m || m == `Deformation
      | none => false
    if included && !info.isUnsafe then some n else none
  for n in names do
    for ax in (← collectAxioms n) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Forbidden axiom in {n}: {ax}"
  logInfo m!"PASS: {names.length} safe deformation-step declarations; no sorryAx or additional axioms."
  logInfo "LowDegreeStep and PolynomialBGGInput are proved; the legacy TwoRemainingInputs is equivalent to collision support alone."

noncomputable section
open KhanSL2 KhanSL2.Conditional

#print LowDegreeStep
#check (lowDegreeStep : LowDegreeStep)
#print TwoRemainingInputs
#check (mainStatement_of_twoInputs : TwoRemainingInputs → MainStatement)
#check (remainingInputs_iff_two : RemainingInputs ↔ TwoRemainingInputs)
#check (psi_injective_iff_surj : ∀ B p : ℕ,
  Function.Injective (psi B p) ↔ ∀ S : ℤ, Surj (Current.kDegree p B S))
#print Surj
#check @totalZero_exact
#check @totalOne_exact
#check @dpp_exact
#check @splitMap_D0
#audit_deformation
#print axioms lowDegreeStep
#print axioms mainStatement_of_twoInputs
#print axioms totalZero_exact
#print axioms totalOne_exact

-- The low-degree step is a proved theorem and is no longer a field of RemainingInputs.
#check (KhanSL2.lowDegreeStep : KhanSL2.Conditional.LowDegreeStep)
example (hC : KhanSL2.Conditional.CollisionSupportStep) :
    KhanSL2.Conditional.RemainingInputs := ⟨hC⟩
#print axioms KhanSL2.lowDegreeStep

#check (KhanSL2.Conditional.topTermEquiv : ∀ B : ℕ,
  KhanSL2.Conditional.BGGComplex.Term B B ≃ₗ[KhanSL2.Conditional.CoefficientRing B]
    KhanSL2.Conditional.CoefficientRing B)
#print axioms KhanSL2.Conditional.topTermEquiv
