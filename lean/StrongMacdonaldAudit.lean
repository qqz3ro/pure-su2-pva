module

import all KhanSL2.Basic
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
import all KhanSL2.StrongMacdonald.Algebra
import all KhanSL2.StrongMacdonald.DiffOp
import all KhanSL2.StrongMacdonald.Derivation
import all KhanSL2.StrongMacdonald.OrderCalculus
import all KhanSL2.StrongMacdonald.MkDer
import all KhanSL2.StrongMacdonald.HomDer
import all KhanSL2.StrongMacdonald.Local
import all KhanSL2.StrongMacdonald.Operators
import all KhanSL2.StrongMacdonald.Laplacian
import all KhanSL2.StrongMacdonald.LapGen
import all KhanSL2.StrongMacdonald.NormalForm
import all KhanSL2.StrongMacdonald.LapSigPsi
import all KhanSL2.StrongMacdonald.LapPsiPsi
import all KhanSL2.StrongMacdonald.LapMain
import all KhanSL2.StrongMacdonald.Herm
import all KhanSL2.StrongMacdonald.HermBasic
import all KhanSL2.StrongMacdonald.HermDer
import all KhanSL2.StrongMacdonald.HermPairs
import all KhanSL2.StrongMacdonald.HermLap
import all KhanSL2.StrongMacdonald.Grading
import all KhanSL2.StrongMacdonald.Subst
import all KhanSL2.StrongMacdonald.ExpDer
import all KhanSL2.StrongMacdonald.JetAlg
import all KhanSL2.StrongMacdonald.Orbit
import all KhanSL2.StrongMacdonald.OrbitMoves
import all KhanSL2.StrongMacdonald.Torus
import all KhanSL2.StrongMacdonald.Project
import all KhanSL2.StrongMacdonald.Invariants
import all KhanSL2.StrongMacdonald.Harmonic
import all KhanSL2.StrongMacdonald.Generators
import all KhanSL2.StrongMacdonald.SliceRing
import all KhanSL2.StrongMacdonald.DbarSquare
import all KhanSL2.StrongMacdonald.HodgeAbstract
import all KhanSL2.StrongMacdonald.Hodge
import all KhanSL2.StrongMacdonald
import all StrongMacdonald

public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

/-! Audit of FGT Theorem B for `𝔰𝔩₂` (`KhanSL2/StrongMacdonald/`).

Every project module in the import closure is imported with `import all`, so private proof
bodies are visible to the axiom collector. The audit checks that the key results are proved
theorems (or definitions) and that no declaration of the listed developments uses an axiom
beyond `propext`, `Classical.choice` and `Quot.sound`. -/

open Lean Elab Command

elab "#audit_strong_macdonald" : command => do
  let env ← getEnv
  let isProjectModule := fun (name : Name) =>
    (`KhanSL2).isPrefixOf name || name == `StrongMacdonald || name == `Collision
  for imported in env.header.modules do
    if isProjectModule imported.module && !imported.importAll then
      throwError "Missing proof bodies in {imported.module}"
  for n in #[`KhanSL2.StrongMacdonald.lap_eq_box_D_K,
      `KhanSL2.StrongMacdonald.dbar_mul_dbar,
      `KhanSL2.StrongMacdonald.mem_harm_iff,
      `KhanSL2.StrongMacdonald.harmToCohom_bijective,
      `KhanSL2.StrongMacdonald.eq_zero_of_slicePt,
      `KhanSL2.StrongMacdonald.reach_slice_one,
      `KhanSL2.StrongMacdonald.exists_free_preimage,
      `KhanSL2.StrongMacdonald.Gmap_injOn,
      `KhanSL2.StrongMacdonald.harm_free,
      `KhanSL2.StrongMacdonald.Sgen_mem_harm,
      `KhanSL2.StrongMacdonald.Egen_mem_harm] do
    match env.find? n with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected proved theorem {n}"
  let names := env.constants.toList.filterMap fun (n, info) =>
    let included := match env.getModuleIdxFor? n with
      | some idx =>
        let m := env.header.moduleNames[idx.toNat]!
        (`KhanSL2.StrongMacdonald).isPrefixOf m || (`StrongMacdonald).isPrefixOf m
      | none => false
    if included && !info.isUnsafe then some n else none
  for n in names do
    for ax in (← collectAxioms n) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Forbidden axiom in {n}: {ax}"
  logInfo m!"PASS: {names.length} safe declarations; no sorryAx or additional axioms."

#audit_strong_macdonald

open KhanSL2.StrongMacdonald

#check @lap_eq_box_D_K
#check @dbar_mul_dbar
#check @mem_harm_iff
#check @harmEquivCohom
#check @eq_zero_of_slicePt
#check @harm_free
#print axioms harm_free
#print axioms harmEquivCohom
