module

import all MainProofAudit
import all Final

public import Lean.Elab.Command
public import Lean.Util.CollectAxioms

/-! Checks the new release entry point in addition to the unchanged full audit. -/

#check (KhanSL2.mainStatement : KhanSL2.MainStatement)
#check (KhanSL2.mainStatement_explicit :
  KhanSL2.IsGradedDifferentialPVAIsomorphism
    KhanSL2.sourceData KhanSL2.Source.bracket
    KhanSL2.targetData KhanSL2.targetBracket KhanSL2.phi)
#check (KhanSL2.phi_bijective : Function.Bijective KhanSL2.phi)
#print axioms KhanSL2.mainStatement_explicit

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  match env.find? `KhanSL2.mainStatement_explicit with
  | some (.thmInfo _) => pure ()
  | _ => throwError "The vfinal entry point is not a proved theorem."
  for ax in (← collectAxioms `KhanSL2.mainStatement_explicit) do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Forbidden axiom in vfinal theorem: {ax}"
  logInfo "PASS: vfinal explicit theorem and original statement; only standard foundational axioms."
