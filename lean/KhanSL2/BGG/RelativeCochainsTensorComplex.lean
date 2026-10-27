module

public import KhanSL2.BGG.RelativeCochainsTensor
public import KhanSL2.BGG.RelativeCochainsTermComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KhanSL2.BGG.RelativeCochains
open scoped RelativeCochains

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]

/-- The actual BGG cochain differential, transported to invariant tensor coordinates. -/
def invariantTensorDifferential (p : ℕ) :
    InvariantTensor M p →ₗ[ℂ] InvariantTensor M (p+1) :=
  (inducedInvariantTensorEquiv M (p+1)).toLinearMap.comp
    ((termDifferential M p).comp (inducedInvariantTensorEquiv M p).symm.toLinearMap)

@[simp] theorem invariantTensorDifferential_apply (p : ℕ) (t : InvariantTensor M p) :
    invariantTensorDifferential M p t = inducedInvariantTensorEquiv M (p+1)
      (termDifferential M p ((inducedInvariantTensorEquiv M p).symm t)) := rfl

/-- The invariant tensor differential squares to zero because the specified
relative BGG differential does. -/
@[simp] theorem invariantTensorDifferential_square_zero (p : ℕ) (t : InvariantTensor M p) :
    invariantTensorDifferential M (p+1) (invariantTensorDifferential M p t) = 0 := by
  simp only [invariantTensorDifferential_apply, LinearEquiv.symm_apply_apply,
    termDifferential_square_zero, map_zero]

/-- The harmonic-to-invariant-tensor identification is a degreewise chain map. -/
theorem harmonicInvariantTensorEquiv_differential (p : ℕ) (f : harmonicDegree M p) :
    harmonicInvariantTensorEquiv M (p+1) (harmonicDegreeDifferential M p f) =
      invariantTensorDifferential M p (harmonicInvariantTensorEquiv M p f) := by
  simp only [harmonicInvariantTensorEquiv_eq_induced, invariantTensorDifferential_apply,
    LinearEquiv.symm_apply_apply, harmonicInducedEquiv_differential]

end KhanSL2.BGG.RelativeCochains