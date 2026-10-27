module

public import KhanSL2.BGG.RootExteriorCurrent
public import KhanSL2.BGG.ExteriorAction

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual constant sl₂ action on positive current exterior algebra. -/

noncomputable section
open scoped TensorProduct BigOperators

namespace KhanSL2.BGG

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Constants act on the positive ideal by the actual current Lie bracket. -/
def positiveAdjoint : G →ₗ⁅ℂ⁆ Module.End ℂ positive :=
  (LieModule.toEnd ℂ Current positive).comp constant

@[simp] theorem positiveAdjoint_coe (x : G) (u : positive) :
    (positiveAdjoint x u : Current) = ⁅constant x, (u : Current)⁆ := rfl

@[simp] theorem positiveAdjoint_positiveMode (x y : G) (n : ℕ) :
    positiveAdjoint x (positiveMode n y) = positiveMode n ⁅x, y⁆ := by
  apply Subtype.ext
  change ⁅constant x, mode (n + 1) y⁆ = mode (n + 1) ⁅x, y⁆
  rw [constant_apply, mode_lie, zero_add]

/-- Root-mode coordinates of the actual constant adjoint representation. -/
def rootModeAction : G →ₗ⁅ℂ⁆ Module.End ℂ (RootMode →₀ ℂ) :=
  positiveBasis.repr.lieConj.toLieHom.comp positiveAdjoint

@[simp] theorem rootModeAction_repr (x : G) (u : positive) :
    rootModeAction x (positiveBasis.repr u) = positiveBasis.repr (positiveAdjoint x u) := by
  simp [rootModeAction, LinearEquiv.conj_apply]

@[simp] theorem rootModeAction_single (x : G) (i : RootMode) :
    rootModeAction x (Finsupp.single i 1) = positiveBasis.repr (positiveAdjoint x (positiveBasis i)) := by
  rw [← positiveBasis.repr_self i, rootModeAction_repr]

/-- Constants change only the root color, preserving the current mode. -/
theorem rootModeAction_single_eq_sum (x : G) (n : ℕ) (a : Fin 3) :
    rootModeAction x (Finsupp.single (n, a) 1) =
      ∑ b : Fin 3, rootBasis.repr ⁅x, rootBasis a⁆ b • Finsupp.single (n, b) 1 := by
  rw [rootModeAction_single, positiveBasis_apply, positiveAdjoint_positiveMode]
  conv_lhs => rw [← rootBasis.sum_repr ⁅x, rootBasis a⁆]
  rw [map_sum, map_sum]
  simp only [map_smul, ← positiveBasis_apply, positiveBasis.repr_self]
/-- The resulting genuine Lie representation on all concrete exterior degrees. -/
def rootExteriorAction : G →ₗ⁅ℂ⁆ Module.End ℂ RootExterior :=
  FiniteExterior.infinitesimalLieMap.comp rootModeAction

@[simp] theorem rootExteriorAction_generator (x : G) (i : RootMode) :
    rootExteriorAction x (FiniteExterior.generator i) =
      FiniteExterior.generatorLinear (rootModeAction x (Finsupp.single i 1)) := by
  exact FiniteExterior.infinitesimalAction_generator (rootModeAction x) i

/-- Explicit color replacement on a single exterior generator. -/
theorem rootExteriorAction_generator_eq_sum (x : G) (n : ℕ) (a : Fin 3) :
    rootExteriorAction x (FiniteExterior.generator (n, a)) =
      ∑ b : Fin 3, rootBasis.repr ⁅x, rootBasis a⁆ b • FiniteExterior.generator (n, b) := by
  rw [rootExteriorAction_generator, rootModeAction_single_eq_sum, map_sum]
  simp only [map_smul, FiniteExterior.generatorLinear_single, one_smul]
/-- The vector-space embedding uses exactly the coordinates in the action. -/
theorem rootCurrentGenerator_eq :
    rootCurrentGenerator = FiniteExterior.generatorLinear.comp positiveBasis.repr.toLinearMap := by
  apply positiveBasis.ext
  intro i
  obtain ⟨n, a⟩ := i
  rw [rootCurrentGenerator_positiveBasis, LinearMap.comp_apply,
    LinearEquiv.coe_coe, positiveBasis.repr_self,
    FiniteExterior.generatorLinear_single, one_smul]

/-- The exterior action agrees with the actual Lie bracket on degree one. -/
theorem rootExteriorAction_currentGenerator (x : G) (u : positive) :
    rootExteriorAction x (rootCurrentGenerator u) = rootCurrentGenerator (positiveAdjoint x u) := by
  simp only [rootCurrentGenerator_eq, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change FiniteExterior.infinitesimalAction (rootModeAction x)
    (FiniteExterior.generatorLinear (positiveBasis.repr u)) = _
  rw [FiniteExterior.infinitesimalAction_generatorLinear, rootModeAction_repr]

@[simp] theorem rootModeAction_h_single (i : RootMode) :
    rootModeAction MatrixSL2.h (Finsupp.single i 1) = rootWeight i.2 • Finsupp.single i 1 := by
  obtain ⟨n, a⟩ := i
  rw [rootModeAction_single, positiveBasis_apply, positiveAdjoint_positiveMode,
    lie_h_rootBasis, map_smul, map_smul, ← positiveBasis_apply, positiveBasis.repr_self]

/-- The actual Cartan action has twice the additive support half-weight. -/
theorem rootExteriorAction_h_monomial (s : Finset RootMode) :
    rootExteriorAction MatrixSL2.h (FiniteExterior.monomial s) =
      (2 * (rootMonomialWeight s : ℂ)) • FiniteExterior.monomial s := by
  change FiniteExterior.infinitesimalAction (rootModeAction MatrixSL2.h)
    (FiniteExterior.monomial s) = _
  rw [FiniteExterior.infinitesimalAction_monomial_of_diagonal _
    (fun i => rootWeight i.2) rootModeAction_h_single]
  congr 1
  simp only [rootWeight_eq_twice_halfWeight, ← Finset.mul_sum, ← Int.cast_sum]
  rfl

instance : LieRingModule G RootExterior :=
  LieRingModule.compLieHom RootExterior rootExteriorAction

instance : LieModule ℂ G RootExterior :=
  LieModule.compLieHom RootExterior rootExteriorAction

theorem root_lie_h_monomial (s : Finset RootMode) :
    ⁅MatrixSL2.h, FiniteExterior.monomial s⁆ =
      (2 * (rootMonomialWeight s : ℂ)) • FiniteExterior.monomial s :=
  rootExteriorAction_h_monomial s

end KhanSL2.BGG