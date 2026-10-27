module

public import KhanSL2.Factorization.BalancedScalarDiagram

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex
namespace KhanSL2.Factorization
open BGG SymmetricFamily NonnegativeCone

variable (A : Type) [CommRing A] [Algebra ℂ A]
variable (M N : Type) [AddCommGroup M] [Module ℂ M] [Module A M] [IsScalarTower ℂ A M]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent A M]
  [AddCommGroup N] [Module ℂ N] [Module A N] [IsScalarTower ℂ A N]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent A N]
variable (K : Type) [CommRing K] [Algebra A K] [Algebra ℂ K] [IsScalarTower ℂ A K]

/-- Exact scalar-extension compatibility also reflects quasi-isomorphisms of the
actual specialized balanced shuffle. This is an isomorphism of chain maps, not
an ordinary homology-base-change claim. -/
theorem balancedShuffleComplex_scalar_quasiIso_of_specialized
    [QuasiIso (balancedShuffleComplex K (CoefficientBaseChange A M K) (CoefficientBaseChange A N K))] :
    QuasiIso (scalarMap K (balancedShuffleComplex A M N)) := by
  have h : QuasiIso ((scalarMap K (balancedShuffleComplex A M N)) ≫
      (balancedScalarTargetIso A M N K).hom) := by
    rw [balancedShuffleComplex_scalar]
    infer_instance
  let := h
  exact quasiIso_of_comp_right _ (balancedScalarTargetIso A M N K).hom

end KhanSL2.Factorization
