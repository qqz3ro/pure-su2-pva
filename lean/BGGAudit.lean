module

import all KhanSL2.Basic
import all KhanSL2.CurrentAlgebra
import all KhanSL2.BGG.Current
import all KhanSL2.BGG.CurrentCoordinates
import all KhanSL2.BGG.CurrentPositive
import all KhanSL2.BGG.CurrentBasis
import all KhanSL2.ExteriorAlgebra
import all KhanSL2.ExteriorSigns
import all KhanSL2.ExteriorParity
import all KhanSL2.ExteriorRing
import all KhanSL2.ExteriorSupercomm
import all KhanSL2.Injectivity.ExteriorSubstitution
import all KhanSL2.BGG.ExteriorModel
import all KhanSL2.CE
import all KhanSL2.Cocycles
import all KhanSL2.CEDerivationBasics
import all KhanSL2.BasisGrading
import all KhanSL2.CochainGrading
import all KhanSL2.CEDegrees
import all KhanSL2.CEExterior
import all KhanSL2.PVA
import all KhanSL2.CochainSupercomm
import all KhanSL2.ExteriorContraction
import all KhanSL2.ExteriorDerivation
import all KhanSL2.CELeibniz
import all KhanSL2.CESeries
import all KhanSL2.CESquareZero
import all KhanSL2.BGG.PositiveCE
import all KhanSL2.Injectivity.FinitePairing
import all KhanSL2.Injectivity.FiniteSupport
import all KhanSL2.BGG.PositiveBoundary
import all KhanSL2.ColorBasis
import all KhanSL2.BGG.FreeCEBasis
import all KhanSL2.BGG.CurrentScaling
import all KhanSL2.BGG.WordGrading
import all KhanSL2.BGG.Augmentation
import all KhanSL2.BGG.UEGeneration
import all KhanSL2.BGG.EnvelopingGrading
import all KhanSL2.BGG.Induced
import all KhanSL2.BGG.FreeCE
import all KhanSL2.BGG.PositiveBoundaryAdjoint
import all KhanSL2.BGG.PositiveLaplacianBasics
import all KhanSL2.BGG.ExteriorSecondOrder
import all KhanSL2.BGG.ExteriorSecondOrderCalculus
import all KhanSL2.BGG.PositiveLaplacianOrder
import all KhanSL2.BGG.PositiveBoundaryProducts
import all KhanSL2.BGG.PositiveLaplacianPairs
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
import all KhanSL2.CEInvariantBasics
import all KhanSL2.CEEquivariance
import all KhanSL2.BGG.ColorRootEquivariance
import all KhanSL2.BGG.ExteriorEuler
import all KhanSL2.BGG.ColorRootGrading
import all KhanSL2.BGG.PositiveCEParity
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
import all KhanSL2.BGG.PositiveBoundaryEquivariance
import all KhanSL2.BGG.PositiveContractionGrading
import all KhanSL2.BGG.PositiveEnergyScale
import all KhanSL2.BGG.FreeCEEnergy
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
import all KhanSL2.BGG.PerturbationEquivariance
import all KhanSL2.BGG.PositiveTransferEnergy
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
import all KhanSL2.BGG.TermPBWGrading
import all KhanSL2.BGG.TermPBWFree
import all KhanSL2.BGG.HarmonicTensorTerms
import all KhanSL2.BGG.HarmonicEnergy
import all KhanSL2.BGG.FreeCEEnergyAugmentation
import all KhanSL2.BGG.FreeCEPBW
import all KhanSL2.BGG.PolynomialKoszulFinite
import all KhanSL2.BGG.PolynomialKoszulHomotopy
import all KhanSL2.BGG.FreeCEPBWAugmentation
import all KhanSL2.BGG.PolynomialKoszulGrading
import all KhanSL2.BGG.FreeCEDegree
import all KhanSL2.BGG.PolynomialKoszulTensor
import all KhanSL2.BGG.PolynomialKoszulFiltration
import all KhanSL2.BGG.FreeCELowering
import all KhanSL2.BGG.FreeCEAugmentationModule
import all KhanSL2.BGG.FilteredCorrection
import all KhanSL2.BGG.FreeCEExactness
import all KhanSL2.BGG.ContractionGradedExactness
import all KhanSL2.BGG.HarmonicResolution
import all KhanSL2.BGG.PositiveTransferDegreeBase
import all KhanSL2.BGG.PositiveTransferDegree
import all KhanSL2.BGG.FreeCEActualDegree
import all KhanSL2.BGG.HarmonicResolutionDegree
import all KhanSL2.BGG.TermPBWMorphism
import all KhanSL2.BGG.TermResolution
import all KhanSL2.BGG.FreeCEEquivarianceAction
import all KhanSL2.BGG.HarmonicTensorEquivariance
import all KhanSL2.BGG.FreeCEEquivarianceContraction
import all KhanSL2.BGG.FreeCEEquivariance
import all KhanSL2.BGG.PositiveTransferEquivariance
import all KhanSL2.BGG.TermResolutionEquivariance
import all KhanSL2.BGG.TermResolutionEnergy
import all KhanSL2.BGG.FreeCEAugmentationEquivariance
import all KhanSL2.BGG.TermResolutionAugmentation
import all KhanSL2.BGG.PositiveUEFiniteEnergy
import all KhanSL2.BGG.TermFiniteEnergy
import all KhanSL2.BGG.TermResolutionGradedExactness
import all KhanSL2.BGG.RelativeCochainsBasic
import all KhanSL2.BGG.RelativeCoefficientAction
import all KhanSL2.BGG.TermEnergyLie
import all KhanSL2.BGG.FiniteSl2Splitting
import all KhanSL2.BGG.TermRelativeAdmissibility
import all KhanSL2.BGG.RelativeBGG
import all KhanSL2.BGG.RelativeCochains
import all KhanSL2.BGG.RelativeCochainsTransfer
import all KhanSL2.BGG.RelativeCochainsDegree
import all KhanSL2.BGG.ContractionHomology
import all KhanSL2.BGG.ContractionDegreeHomology
import all KhanSL2.BGG.RelativeCochainsCohomology
import all KhanSL2.BGG.CoefficientDual
import all KhanSL2.BGG.CoefficientTensorInvariants
import all KhanSL2.BGG.RelativeCochainsCoefficients
import all KhanSL2.BGG.RelativeCochainsInduced
import all KhanSL2.BGG.RelativeCochainsTensor
import all KhanSL2.BGG.RelativeCochainsTermComplex
import all KhanSL2.BGG.RelativeCochainsTensorComplex
public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

open Lean Elab Command

elab "#audit_relative_bgg" : command => do
  let env ← getEnv
  for imported in env.header.modules do
    if (`KhanSL2).isPrefixOf imported.module && !imported.importAll then
      throwError "Audit must import all project proof bodies: {imported.module}."
  for name in #[`KhanSL2.BGG.relative_bgg_resolution,
      `KhanSL2.BGG.TermResolution.exact_differentials,
      `KhanSL2.BGG.TermResolution.exact_differential_augmentation,
      `KhanSL2.BGG.TermResolution.augmentation_surjective,
      `KhanSL2.BGG.TermResolution.differential_mem_termPiece,
      `KhanSL2.BGG.TermResolution.exact_energyDifferentials,
      `KhanSL2.BGG.termsRelativelyProjective,
      `KhanSL2.BGG.TermResolution.relative_admissibility,
      `KhanSL2.BGG.RelativeCochains.relative_cohomology_computed_by_bgg,
      `KhanSL2.BGG.RelativeCochains.harmonicInducedEquiv_differential,
      `KhanSL2.BGG.RelativeCochains.invariantTensorDifferential_square_zero,
      `KhanSL2.BGG.finite_nonzero_termPiece_degrees] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "{name} must be a proved theorem."
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`KhanSL2).isPrefixOf ((privateToUserName? name).getD name) && !info.isUnsafe
    then some name else none
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "Forbidden axiom in {name}: {axiomName}"
  logInfo m!"PASS: {names.length} safe project declarations; no sorryAx or additional axioms."
  logInfo "The actual graded relative BGG resolution, including all-degree exactness and relative projectivity, is proved."

#audit_relative_bgg
#check KhanSL2.BGG.relative_bgg_resolution
#print axioms KhanSL2.BGG.relativeBGGResolution
#print axioms KhanSL2.BGG.relative_bgg_resolution
#print axioms KhanSL2.BGG.TermResolution.exact_energyDifferentials
#print axioms KhanSL2.BGG.RelativeCochains.cohomologyEquiv
#print axioms KhanSL2.BGG.RelativeCochains.inducedInvariantTensorEquiv

#print axioms KhanSL2.BGG.TermResolution.relative_admissibility
