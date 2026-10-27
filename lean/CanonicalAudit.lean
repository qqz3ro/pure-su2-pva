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
public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

open Lean Elab Command

elab "#audit_canonical_map" : command => do
  let env ← getEnv
  for imported in env.header.modules do
    if (`KhanSL2).isPrefixOf imported.module && !imported.importAll then
      throwError "Audit must import all proof bodies for {imported.module}."
  if env.contains `KhanSL2.MainStatement then
    throwError "The canonical map must not import the unproved main proposition."
  for name in #[`KhanSL2.phi, `KhanSL2.phiExpression, `KhanSL2.phiPVAMap] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "{name} must be a constructed definition."
  for name in #[`KhanSL2.phi_well_defined, `KhanSL2.phi_mk,
      `KhanSL2.phi_X0, `KhanSL2.phi_Y0, `KhanSL2.phi_mul,
      `KhanSL2.phi_translation, `KhanSL2.phi_degree,
      `KhanSL2.phi_bracket, `KhanSL2.phi_unique] do
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
  logInfo m!"PASS: {names.length} kernel-safe declarations audited; no additional axioms."
  logInfo "The explicit phi and all graded PVA morphism laws are constructed independently of MainStatement."

#check KhanSL2.phi
#check KhanSL2.phi_well_defined
#check KhanSL2.phi_X0
#check KhanSL2.phi_Y0
#check KhanSL2.phiPVAMap
#check KhanSL2.phi_unique
#audit_canonical_map
#print axioms KhanSL2.phi
#print axioms KhanSL2.phi_bracket
