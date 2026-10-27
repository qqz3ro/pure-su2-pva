module

public import KhanSL2.Macdonald.Evaluation
public import TauCeti.Algebra.Lie.DirectSum

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Evaluation commutes with the original external direct sum, on the nose
on every vector and with the prescribed current action. -/
noncomputable section
open scoped DirectSum
namespace KhanSL2.Macdonald

/-- The actual evaluation of a direct sum is the direct sum of the evaluations. -/
def evaluationDirectSumEquiv (a : ℂ) {ι : Type*} (V : ι → Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, LieRingModule BGG.G (V i)] [∀ i, LieModule ℂ BGG.G (V i)] :
    Evaluation a (⨁ i, V i) ≃ₗ⁅ℂ,BGG.Current⁆ ⨁ i, Evaluation a (V i) where
  __ := LinearEquiv.refl ℂ (⨁ i, V i)
  map_lie' {x m} := by
    apply DFinsupp.ext
    intro i
    rfl

end KhanSL2.Macdonald
