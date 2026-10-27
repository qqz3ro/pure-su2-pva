module

-- Import proof bodies, including private project declarations, for the audit.
import all KhanSL2.Basic
import all KhanSL2.Source
import all KhanSL2.PVA
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
public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

open Lean Elab Command

elab "#audit_source_pva" : command => do
  let env ← getEnv
  for imported in env.header.modules do
    if (`KhanSL2).isPrefixOf imported.module && !imported.importAll then
      throwError "Audit must import all proof bodies for {imported.module}."
  if env.contains `KhanSL2.MainStatement || env.contains `KhanSL2.Cohomology then
    throwError "The standalone source audit must not import the target construction."
  match env.find? `KhanSL2.source_isPVA with
  | some (.thmInfo _) => pure ()
  | _ => throwError "source_isPVA must be a proved theorem."
  let names := env.constants.toList.filterMap fun (name, info) =>
    if (`KhanSL2).isPrefixOf ((privateToUserName? name).getD name) && !info.isUnsafe
    then some name else none
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in names do
    for axiomName in (← collectAxioms name) do
      unless allowed.contains axiomName do
        throwError "Forbidden axiom in {name}: {axiomName}"
  logInfo m!"PASS: {names.length} kernel-safe source declarations audited; no additional axioms."
  logInfo "The complete source PVA theorem is proved independently of the cohomology target."

#check KhanSL2.source_isPVA
#check KhanSL2.source_pva_exists
#audit_source_pva
#print axioms KhanSL2.source_isPVA
#print axioms KhanSL2.source_pva_exists
