module

public import KhanSL2.BGG.CoefficientTensorInvariants
public import KhanSL2.BGG.RelativeCochainsInduced

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.RelativeCochains
open scoped RelativeCochains

-- Invariants use the diagonal tensor action, including the coefficient factor.
attribute [local instance 2000] TensorProduct.LieModule.lieRingModule
attribute [local instance 2000] TensorProduct.LieModule.lieModule

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]

/-- Invariant tensors for the actual constant action on the coefficient module. -/
abbrev InvariantTensor (p : ℕ) :=
  ↥(LieModule.maxTrivSubmodule ℂ G (M ⊗[ℂ] Coefficient p))

/-- Degree-p harmonic cochains identified with actual invariant tensors. -/
def harmonicInvariantTensorEquiv (p : ℕ) :
    harmonicDegree M p ≃ₗ[ℂ] InvariantTensor M p :=
  (harmonicLieHomEquiv M p).trans (coefficientTensorInvariantsEquiv p M).symm

/-- Hom from the actual induced BGG term identified with invariant tensors. -/
def inducedInvariantTensorEquiv (p : ℕ) :
    (Term p →ₗ[Enveloping] M) ≃ₗ[ℂ] InvariantTensor M p :=
  ((inducedCoefficientEquiv M p).trans (coefficientHomLieEquiv M (Coefficient p))).trans
    (coefficientTensorInvariantsEquiv p M).symm

/-- The harmonic and induced descriptions give the same invariant tensor. -/
theorem harmonicInvariantTensorEquiv_eq_induced (p : ℕ) (f : harmonicDegree M p) :
    harmonicInvariantTensorEquiv M p f =
      inducedInvariantTensorEquiv M p (harmonicInducedEquiv M p f) := by
  simp only [harmonicInvariantTensorEquiv, harmonicLieHomEquiv, inducedInvariantTensorEquiv,
    harmonicInducedEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

end KhanSL2.BGG.RelativeCochains
