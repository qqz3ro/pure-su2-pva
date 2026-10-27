module

-- Import proof bodies, including private project declarations, for the audit.
import all KhanSL2.Basic
import all KhanSL2.Source
import all KhanSL2.PVA
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
import all KhanSL2.CochainSupercomm
import all KhanSL2.ExteriorContraction
import all KhanSL2.ExteriorDerivation
import all KhanSL2.CELeibniz
import all KhanSL2.CEConvolutionArithmetic
import all KhanSL2.CETranslationGenerator
import all KhanSL2.CESeries
import all KhanSL2.CESquareZero
import all KhanSL2.CEInvariantBasics
import all KhanSL2.CEEquivariance
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
import all KhanSL2.GradingDecomposition
import all KhanSL2.CohomologyGrading
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
import all KhanSL2.PVAIsomorphism
import all KhanSL2.CurrentAlgebra
import all KhanSL2.ColorBasis
import all KhanSL2.MainStatement
import all KhanSL2.Injectivity.ExteriorSubstitution
import all KhanSL2.Injectivity.CartanRestriction
import all KhanSL2.Injectivity.FinitePairing
import all KhanSL2.Injectivity.CartanContraction
import all KhanSL2.Injectivity.RootCurrent
import all KhanSL2.Injectivity.CurrentAdjoint
import all KhanSL2.Injectivity.ChainPairing
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
import all KhanSL2.InjectivityMainStatement
import all KhanSL2.Injectivity.RootKoszulCycles
import all KhanSL2.Chains.Transpose
import all KhanSL2.Chains.Coinvariant
import all KhanSL2.Chains.Dictionary
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
import all KhanSL2.DictionaryStatement
import all KhanSL2
public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

open Lean Elab Command

elab "#audit_khan_sl2" : command => do
  let env ← getEnv
  for imported in env.header.modules do
    if (`KhanSL2).isPrefixOf imported.module && !imported.importAll then
      throwError "Audit must import all proof bodies for {imported.module}."
  match env.find? `KhanSL2.MainStatement with
  | some (.defnInfo info) =>
    unless info.type.isProp do
      throwError "MainStatement must have type Prop."
  | _ => throwError "MainStatement must be a definition, not an axiom or theorem."
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`KhanSL2).isPrefixOf ((privateToUserName? name).getD name) && !info.isUnsafe
    then some name else none
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "Forbidden axiom in {name}: {axiomName}"
  logInfo m!"PASS: {names.length} kernel-safe KhanSL2 declarations audited; no additional axioms."
  logInfo "This foundation audit checks the proposition and canonical map; MainProofAudit checks the completed theorem."

/-- info: KhanSL2.MainStatement : Prop -/
#guard_msgs in
#check KhanSL2.MainStatement

#audit_khan_sl2
#check KhanSL2.phi
#check KhanSL2.phi_well_defined
#check KhanSL2.phiPVAMap
#check KhanSL2.mainStatement_iff_bijective
#print axioms KhanSL2.MainStatement
#print axioms KhanSL2.phi
