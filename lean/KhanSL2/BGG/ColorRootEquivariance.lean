module

public import KhanSL2.BGG.ColorRoot
public import KhanSL2.CEEquivariance

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The explicit color/root equivalence intertwines the actual constant actions,
and the pure-positive CE differential is a morphism of sl₂ representations. -/

noncomputable section
open scoped BigOperators
namespace KhanSL2.BGG.PositiveCE

/-- The restriction of the original concrete color action to pure positive ghosts. -/
def colorAction (a : Fin 3) : Module.End ℂ Cochain :=
  projection.toLinearMap.comp ((KhanSL2.colorAction a).comp inclusion.toLinearMap)

@[simp] theorem colorAction_apply (a : Fin 3) (u : Cochain) :
    colorAction a u = projection (KhanSL2.colorAction a (inclusion u)) := rfl

@[simp] theorem colorAction_one (a : Fin 3) : colorAction a 1 = 0 := by
  simp [KhanSL2.cochain_one_eq]

theorem colorAction_mul (a : Fin 3) (u v : Cochain) :
    colorAction a (u * v) = colorAction a u * v + u * colorAction a v := by
  simp only [colorAction_apply, map_mul, KhanSL2.colorAction_mul, map_add, projection_inclusion]

@[simp] theorem colorAction_generator (a : Fin 3) (m : Mode) :
    colorAction a (FiniteExterior.generator m) =
      ∑ b : Fin 3, epsilon a m.color b • FiniteExterior.generator (⟨m.index, b⟩ : Mode) := by
  simp [KhanSL2.colorGenerator, KhanSL2.Mode.color, KhanSL2.Mode.recolor]

/-- The original constant action preserves the pure-positive coordinate subalgebra. -/
theorem inclusion_colorAction (a : Fin 3) (u : Cochain) :
    inclusion (colorAction a u) = KhanSL2.colorAction a (inclusion u) := by
  refine FiniteExterior.induction_on Mode.code
    (P := fun v => inclusion (colorAction a v) = KhanSL2.colorAction a (inclusion v))
    ?_ ?_ ?_ ?_ ?_ u
  · simp
  · change inclusion (colorAction a 1) = KhanSL2.colorAction a (inclusion 1)
    simp [KhanSL2.cochain_one_eq]
  · intro v w hv hw
    simp only [map_add, hv, hw]
  · intro r v hv
    simp only [map_smul, hv]
  · intro m v hv
    change inclusion (colorAction a (FiniteExterior.generator m * v)) =
      KhanSL2.colorAction a (inclusion (FiniteExterior.generator m * v))
    have hm : inclusion (colorAction a (FiniteExterior.generator m)) =
        KhanSL2.colorAction a (inclusion (FiniteExterior.generator m)) := by
      simp [KhanSL2.colorGenerator, KhanSL2.Mode.color, KhanSL2.Mode.recolor]
    simp only [colorAction_mul, map_mul, map_add, KhanSL2.colorAction_mul, hm, hv]

/-- The already proved CE equivariance descends to pure positive currents. -/
theorem d_colorAction (a : Fin 3) (u : Cochain) :
    d (colorAction a u) = colorAction a (d u) := by
  apply inclusion_injective
  simp only [inclusion_d, inclusion_colorAction, KhanSL2.q_colorAction]

end KhanSL2.BGG.PositiveCE

namespace KhanSL2.BGG.ColorRoot

private theorem root_action_one (x : G) : rootExteriorAction x 1 = 0 :=
  FiniteExterior.infinitesimalAction_one (rootModeAction x)

private theorem root_action_mul (x : G) (u v : RootExterior) :
    rootExteriorAction x (u * v) = rootExteriorAction x u * v + u * rootExteriorAction x v :=
  FiniteExterior.infinitesimalAction_mul (rootModeAction x) u v

private theorem toRoot_colorAction_generator (a : Fin 3) (m : PositiveCE.Mode) :
    toRoot (PositiveCE.colorAction a (FiniteExterior.generator m)) =
      rootExteriorAction (MatrixSL2.color a) (toRoot (FiniteExterior.generator m)) := by
  obtain ⟨n, b⟩ := m
  rw [PositiveCE.colorAction_generator, toRoot_generator, rootExteriorAction_rootAt,
    MatrixSL2.color_bracket]
  simp only [map_sum, map_smul, toRoot_generator]

/-- The specified coordinate map intertwines the existing concrete color action. -/
theorem toRoot_colorAction (a : Fin 3) (u : PositiveCE.Cochain) :
    toRoot (PositiveCE.colorAction a u) = rootExteriorAction (MatrixSL2.color a) (toRoot u) := by
  refine FiniteExterior.induction_on PositiveCE.Mode.code
    (P := fun v => toRoot (PositiveCE.colorAction a v) =
      rootExteriorAction (MatrixSL2.color a) (toRoot v)) ?_ ?_ ?_ ?_ ?_ u
  · simp
  · change toRoot (PositiveCE.colorAction a 1) = rootExteriorAction (MatrixSL2.color a) (toRoot 1)
    rw [PositiveCE.colorAction_one, map_zero, map_one, root_action_one]
  · intro v w hv hw
    simp only [map_add, hv, hw]
  · intro r v hv
    simp only [map_smul, hv]
  · intro m v hv
    change toRoot (PositiveCE.colorAction a (FiniteExterior.generator m * v)) =
      rootExteriorAction (MatrixSL2.color a) (toRoot (FiniteExterior.generator m * v))
    simp only [PositiveCE.colorAction_mul, map_mul, map_add, root_action_mul,
      toRoot_colorAction_generator, hv]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Transport the proved actual sl₂ representation through the explicit color/root equivalence. -/
def positiveAction : G →ₗ⁅ℂ⁆ Module.End ℂ PositiveCE.Cochain :=
  equiv.symm.toLinearEquiv.lieConj.toLieHom.comp rootExteriorAction

@[simp] theorem positiveAction_apply (x : G) (u : PositiveCE.Cochain) :
    positiveAction x u = toColor (rootExteriorAction x (toRoot u)) := rfl

@[simp] theorem positiveAction_color (a : Fin 3) :
    positiveAction (MatrixSL2.color a) = PositiveCE.colorAction a := by
  apply LinearMap.ext
  intro u
  rw [positiveAction_apply, ← toRoot_colorAction]
  exact equiv.symm_apply_apply (PositiveCE.colorAction a u)

/-- The pure-positive CE differential is equivariant for every actual matrix sl₂ element. -/
theorem d_positiveAction (x : G) (u : PositiveCE.Cochain) :
    PositiveCE.d (positiveAction x u) = positiveAction x (PositiveCE.d u) := by
  rw [← MatrixSL2.color_decomposition x]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    positiveAction_color, PositiveCE.d_colorAction]

end KhanSL2.BGG.ColorRoot

namespace KhanSL2.BGG.PositiveCE

attribute [local instance 100] LieRing.ofAssociativeRing

instance : LieRingModule G Cochain := LieRingModule.compLieHom Cochain ColorRoot.positiveAction
instance : LieModule ℂ G Cochain := LieModule.compLieHom Cochain ColorRoot.positiveAction

/-- The concrete differential, now bundled as a proved morphism of actual sl₂ representations. -/
def dLie : Cochain →ₗ⁅ℂ,G⁆ Cochain :=
  { d with map_lie' := fun {x u} => ColorRoot.d_positiveAction x u }

@[simp] theorem dLie_apply (u : Cochain) : dLie u = d u := rfl

end KhanSL2.BGG.PositiveCE