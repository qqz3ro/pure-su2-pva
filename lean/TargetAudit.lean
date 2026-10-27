module

-- Import proof bodies, including private project declarations, for the audit.
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
import all KhanSL2.CEConvolutionArithmetic
import all KhanSL2.CETranslationGenerator
import all KhanSL2.CESeries
import all KhanSL2.CESquareZero
import all KhanSL2.CEInvariantBasics
import all KhanSL2.CEEquivariance
import all KhanSL2.CETranslation
import all KhanSL2.Source
import all KhanSL2.SourceData
import all KhanSL2.Data
import all KhanSL2.CEComplex
import all KhanSL2.LambdaPolynomialLemmas
import all KhanSL2.BCModeKernel
import all KhanSL2.BCFullCE
import all KhanSL2.BCFullKernel
import all KhanSL2.LambdaPolynomialSkew
import all KhanSL2.BCFullBracketDefinition
import all KhanSL2.BCSkewCalculus
import all KhanSL2.BCFullBracketSkew
import all KhanSL2.BCFullGrading
import all KhanSL2.BCFullAlgebra
import all KhanSL2.BCFullBracketDegree
import all KhanSL2.BCFullBracketLaws
import all KhanSL2.BCFullGeneration
import all KhanSL2.BCFullBracketSesqui
import all KhanSL2.SourceGeneration
import all KhanSL2.SourceSupercomm
import all KhanSL2.SourceJacobiExtension
import all KhanSL2.JacobiTranslation
import all KhanSL2.JacobiPermutation
import all KhanSL2.JacobiLastPermutation
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
import all KhanSL2.PVAMap
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
public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

open Lean Elab Command

elab "#audit_target_pva" : command => do
  let env ← getEnv
  for imported in env.header.modules do
    if (`KhanSL2).isPrefixOf imported.module && !imported.importAll then
      throwError "Audit must import all proof bodies for {imported.module}."
  if env.contains `KhanSL2.MainStatement then
    throwError "The target proof must not import the unproved main proposition."
  for name in #[`KhanSL2.q_square_zero, `KhanSL2.relativeComplex_laws,
      `KhanSL2.cochain_isPVA, `KhanSL2.relativeBracket_compatibility,
      `KhanSL2.target_isPVA, `KhanSL2.target_isInduced] do
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
  logInfo m!"PASS: {names.length} kernel-safe target-foundation declarations audited; no additional axioms."
  logInfo "The concrete CE complex and induced target PVA are proved independently of MainStatement."

#check KhanSL2.q_square_zero
#check KhanSL2.relativeComplex_laws
#check KhanSL2.target_isPVA
#check KhanSL2.target_isInduced
#audit_target_pva
#print axioms KhanSL2.q_square_zero
#print axioms KhanSL2.relativeComplex_laws
#print axioms KhanSL2.target_isPVA
#print axioms KhanSL2.target_isInduced
