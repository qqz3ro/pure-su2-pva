module

import all KhanSL2.BGGBridge.BaseChange
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
import all KhanSL2.CEInvariantBasics
import all KhanSL2.CEEquivariance
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
import all KhanSL2.BGGBridgeStatement
import all KhanSL2.BGGBridge.CoefficientWeights
import all KhanSL2.BGGBridge.CoefficientProjection
import all KhanSL2.BGGBridge.TensorCoinvariants
import all KhanSL2.BGGBridge.TermVanishing
import all KhanSL2.Modules.GradedAssembly
import all KhanSL2.Modules.CoefficientOperators
import all KhanSL2.Modules.CoefficientHomology
import all KhanSL2.BGGBridge.CoefficientOps
import all KhanSL2.BGGBridge.CoefficientWindows
import all KhanSL2.BGGBridge.CoefficientComparison
import all KhanSL2.BGGBridge.TopAlternantsMap
import all KhanSL2.BGGBridge.TopLadder
import all KhanSL2.BGGBridge.TopWeights
import all KhanSL2.BGGBridge.TopSpanning
import all KhanSL2.BGG.HarmonicEnergy
import all KhanSL2.BGGBridge.TopGeneratorWindow
import all KhanSL2.BGGBridge.TopPolynomialMap
import all KhanSL2.Modules.PolynomialModels
import all KhanSL2.Modules.WeightedRoots
import all KhanSL2.Modules.PowerSumCoordinates
import all KhanSL2.BGGBridge.TopAlternants
import all KhanSL2.BGGBridge.TopWeightBasis
import all BGGBridge

public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

open Lean Elab Command

/-- Audit every safe project declaration reachable from the BGG bridge (the BGG complex computes
`K p B S`, and the `B = 0` corollary), including the transitive dependencies of its proofs. -/
elab "#audit_bgg_bridge" : command => do
  let env ← getEnv
  for imported in env.header.modules do
    if (`KhanSL2).isPrefixOf imported.module && !imported.importAll then
      throwError "Audit must import all proof bodies for {imported.module}."
  for name in #[`KhanSL2.Current.milestoneBGGBridge,
      `KhanSL2.BGGBridge.cohomology_B_zero,
      `KhanSL2.BGGBridge.finrank_K_trivial,
      `KhanSL2.BGGBridge.finrank_cohomologyPiece_trivial,
      `KhanSL2.BGGBridge.finrank_bggHomology_trivial,
      `KhanSL2.BGGBridge.J_boundary,
      `KhanSL2.BGGBridge.map_J_genRelations,
      `KhanSL2.BGGBridge.mem_genPiece_iff_J,
      `KhanSL2.BGGBridge.boundary_inclusion,
      `KhanSL2.BGGBridge.dHq_comp_dHq,
      `KhanSL2.BGGBridge.bggTerm_eq_bot_of_pos,
      `KhanSL2.BGGBridge.oneClass_ne_zero] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "{name} must be a proved theorem."
  for name in #[`KhanSL2.BGGBridge.kEquivBGG, `KhanSL2.Current.kEquivBGGHomology,
      `KhanSL2.BGGBridge.cN, `KhanSL2.BGGBridge.qcN, `KhanSL2.BGGBridge.relContraction,
      `KhanSL2.BGGBridge.J, `KhanSL2.BGGBridge.exteriorEquiv] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "{name} must be a definition."
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`KhanSL2).isPrefixOf ((privateToUserName? name).getD name) && !info.isUnsafe
    then some name else none
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "Forbidden axiom in {name}: {axiomName}"
  logInfo m!"PASS: {names.length} safe project declarations; no sorryAx or additional axioms."

open KhanSL2 KhanSL2.BGG KhanSL2.Current KhanSL2.BGGBridge

-- These annotations pin the exact statements and definitions.

-- The BGG contraction, base-changed to any `𝔩`-module `N` and passed to `𝔤`-coinvariants.
#check (cN : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] [LieRingModule Current N]
    [LieModule ℂ Current N], TauCeti.LinearSpecialContraction (M := ChainN N) (N := HarmN N)
      (dC N) (dH N))
#check (qcN : ∀ (N : Type) [AddCommGroup N] [Module ℂ N] [LieRingModule Current N]
    [LieModule ℂ Current N], TauCeti.LinearSpecialContraction (M := ChainN N ⧸ relC N)
      (N := HarmN N ⧸ relH N) (dCq N) (dHq N))
example : dH NB = base (rightAction NB) PositiveTransfer.differential := rfl
example : relH NB = ⨆ x : G, LinearMap.range (actH NB x) := rfl
example (x : G) : actH NB x =
    diag (LieModule.toEnd ℂ G PositiveCE.Harmonic x) (LieModule.toEnd ℂ Current NB (constant x)) :=
  rfl

-- The BGG complex and its pieces.
example (p B : ℕ) (S : ℤ) : harmWin p B S = tensorLeft (degH p) ⊓
    Module.End.eigenspace numBH (B : ℂ) ⊓ Module.End.eigenspace dilH ((2 : ℂ) ^ S) := rfl
example (p : ℕ) : degH p = (PositiveCE.harmonicDegree p).toSubmodule := rfl
example (p B : ℕ) (S : ℤ) : bggTerm p B S = (harmWin p B S).map (relH NB).mkQ := rfl
example (p B : ℕ) (S : ℤ) :
    BGGHomology p B S = (bggWindow p B S).homology dHq_comp_dHq := rfl
example (p B : ℕ) (S : ℤ) : (bggWindow p B S).current = bggTerm p B S := rfl
example (p B : ℕ) (S : ℤ) : (bggWindow p B S).previous = bggTerm (p + 1) B S := rfl
#check (dHq_comp_dHq : (dHq NB).comp (dHq NB) = 0)
#check (harmonicDegree_standard : ∀ p : ℕ,
    Nonempty (PositiveCE.harmonicDegree p ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2 * p)))

-- The comparison with M2's chains.
#check (exteriorEquiv : ExteriorAlgebra ℂ plus ≃ₐ[ℂ] PositiveCE.Cochain)
#check (boundary_inclusion : ∀ ω : PositiveCE.Cochain,
    KhanSL2.boundary (PositiveCE.inclusion ω) = PositiveCE.inclusion (PositiveCE.boundary ω))
#check (J_boundary : ∀ ξ : GenChains, J (LieChains.boundary NB ξ) = dC NB (J ξ))
#check (map_J_genRelations : genRelations.map J.toLinearMap = relC NB)
#check (mem_genPiece_iff_J : ∀ (p B : ℕ) (S : ℤ) (ξ : GenChains),
    ξ ∈ genPiece (kDegree p B S) ↔ J ξ ∈ degWin p B S)

-- The bridge.
#check (kEquivBGG : ∀ (p B : ℕ) (S : ℤ), K p B S ≃ₗ[ℂ] BGGHomology p B S)

-- Trivial coefficients.
#check (finrank_K_trivial : ∀ (p : ℕ) (S : ℤ),
    Module.finrank ℂ (K p 0 S) = if p = 0 ∧ S = 0 then 1 else 0)
#check (cohomology_B_zero :
    (∀ (p : ℕ) (S : ℤ), ¬(p = 0 ∧ S = 0) → cohomologyPiece (kDegree p 0 S) = ⊥) ∧
      cohomologyPiece (kDegree 0 0 0) = ℂ ∙ classOf cochainOne one_mem_cycles)
#check (milestoneBGGBridge :
    (∀ (p B : ℕ) (S : ℤ), Nonempty (K p B S ≃ₗ[ℂ] BGGHomology p B S)) ∧
      (dHq NB).comp (dHq NB) = 0 ∧
      (∀ p : ℕ, Nonempty (PositiveCE.harmonicDegree p ≃ₗ⁅ℂ,G⁆ TauCeti.Sl2Std ℂ (2 * p))) ∧
      (∀ (p : ℕ) (S : ℤ), Module.finrank ℂ (K p 0 S) = if p = 0 ∧ S = 0 then 1 else 0) ∧
      (∀ (p : ℕ) (S : ℤ), ¬(p = 0 ∧ S = 0) → cohomologyPiece (kDegree p 0 S) = ⊥) ∧
      cohomologyPiece (kDegree 0 0 0) = ℂ ∙ classOf cochainOne one_mem_cycles)

#audit_bgg_bridge
#print axioms KhanSL2.Current.milestoneBGGBridge
#print axioms KhanSL2.BGGBridge.kEquivBGG
#print axioms KhanSL2.BGGBridge.cohomology_B_zero
#print axioms KhanSL2.BGGBridge.J_boundary

#check (KhanSL2.BGGBridge.bggTerm_eq_bot_of_lt : ∀ B p : ℕ, B < p → ∀ S : ℤ,
  KhanSL2.BGGBridge.bggTerm p B S = ⊥)
#print axioms KhanSL2.BGGBridge.bggTerm_eq_bot_of_lt

#check KhanSL2.BGGBridge.coefficientBGGPower_dHq
#check KhanSL2.BGGBridge.kEquivBGGHomology_coefficientKPower
#print axioms KhanSL2.BGGBridge.kEquivBGGHomology_coefficientKPower
