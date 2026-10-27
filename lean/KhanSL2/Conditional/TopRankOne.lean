module

public import KhanSL2.Conditional.TopCyclicity
public import KhanSL2.Conditional.TopCyclicAlgebra
public import KhanSL2.Conditional.TopComparison

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
namespace KhanSL2.Conditional
open scoped KhanSL2.Conditional

local instance topRankOneTermAddCommGroup (B : ℕ) : AddCommGroup (BGGComplex.Term B B) := inferInstance
local instance topRankOneTermModule (B : ℕ) : Module (CoefficientRing B) (BGGComplex.Term B B) := inferInstance

local instance topRankOneCyclesAddCommGroup (B : ℕ) :
    AddCommGroup (Depth.cycles (BGGComplex.Term B) (bggDifferential B) B) := inferInstance
local instance topRankOneCyclesModule (B : ℕ) :
    Module (CoefficientRing B) (Depth.cycles (BGGComplex.Term B) (bggDifferential B) B) := inferInstance
/-- The actual top BGG term is free of rank one over its fixed coefficient ring.
Its basis vector is the bottom harmonic vector paired with consecutive e modes.
No polynomial-module property or unresolved comparison input is assumed. -/
def topTermEquiv (B : ℕ) : BGGComplex.Term B B ≃ₗ[CoefficientRing B] CoefficientRing B := by
  let P : Submodule (CoefficientRing B) (BGGComplex.Term B B) :=
    Depth.cycles (BGGComplex.Term B) (bggDifferential B) B
  let f : P →ₗ[CoefficientRing B] CoefficientRing B := topCycleMap B
  have hf : Function.Surjective f := topCycleMap_surjective B
  exact cyclicEquivOfSubmoduleSurjective (R := CoefficientRing B) (M := BGGComplex.Term B B)
    (BGGComplex.topGenerator B) (BGGComplex.topGenerator_surjective B) P f hf

/-- The canonical generator has coordinate one in the proved equivalence. -/
theorem topTermEquiv_generator (B : ℕ) : topTermEquiv B (BGGComplex.topGenerator B) = 1 := by
  apply (topTermEquiv B).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change BGGComplex.topGenerator B = (1 : CoefficientRing B) • BGGComplex.topGenerator B
  rw [one_smul]

end KhanSL2.Conditional

