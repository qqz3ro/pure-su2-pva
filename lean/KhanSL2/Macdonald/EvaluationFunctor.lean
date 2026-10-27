module

public import KhanSL2.Macdonald.EvaluationRecognition

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Functoriality of the actual constant restriction and evaluation actions. -/

noncomputable section
namespace KhanSL2.Macdonald

variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

/-- An original current intertwiner also intertwines the actual constant restrictions. -/
def constantRestrictionHom [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
    [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]
    (f : M →ₗ⁅ℂ,BGG.Current⁆ N) : ConstantRestriction M →ₗ⁅ℂ,BGG.G⁆ ConstantRestriction N where
  toLinearMap := (constantRestrictionEquiv N).symm.toLinearMap.comp
    (f.toLinearMap.comp (constantRestrictionEquiv M).toLinearMap)
  map_lie' := fun {x v} => f.map_lie (BGG.constant x) v

/-- An ordinary G-intertwiner is an intertwiner of the evaluation current modules. -/
def evaluationHom [LieRingModule BGG.G M] [LieModule ℂ BGG.G M]
    [LieRingModule BGG.G N] [LieModule ℂ BGG.G N]
    (a : ℂ) (f : M →ₗ⁅ℂ,BGG.G⁆ N) : Evaluation a M →ₗ⁅ℂ,BGG.Current⁆ Evaluation a N where
  toLinearMap := (evaluationEquiv a N).symm.toLinearMap.comp
    (f.toLinearMap.comp (evaluationEquiv a M).toLinearMap)
  map_lie' := fun {x v} => f.map_lie (currentEvaluation a x) v

/-- Actual G-equivalences give actual evaluation-current equivalences. -/
def evaluationLieEquiv [LieRingModule BGG.G M] [LieModule ℂ BGG.G M]
    [LieRingModule BGG.G N] [LieModule ℂ BGG.G N]
    (a : ℂ) (e : M ≃ₗ⁅ℂ,BGG.G⁆ N) : Evaluation a M ≃ₗ⁅ℂ,BGG.Current⁆ Evaluation a N :=
  { ((evaluationEquiv a M).trans e.toLinearEquiv).trans (evaluationEquiv a N).symm with
    map_lie' := fun {x v} => e.toLieModuleHom.map_lie (currentEvaluation a x) v }

end KhanSL2.Macdonald
