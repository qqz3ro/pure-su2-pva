module

public import KhanSL2.BGG.PositiveTransferDegree
public import KhanSL2.BGG.FreeCEEquivariance
public import KhanSL2.BGG.PerturbationEquivariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.PositiveTransfer

/-- The original tensor inclusion intertwines the actual diagonal constant action. -/
theorem base_incl_constantAction (x : G) (u : HarmonicChain) :
    baseContraction.incl (positiveTensorAction PositiveCE.Harmonic x u) =
      FreeCE.constantAction x (baseContraction.incl u) := by
  induction u using TensorProduct.inductionOn with
  | tmul a v =>
    simp only [positiveTensorAction_tmul, FreeCE.constantAction_tmul, map_add,
      baseContraction_incl_tmul, PositiveCE.harmonic_lie_coe]
    rfl
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The original tensor projection intertwines the actual diagonal constant action. -/
theorem base_proj_constantAction (x : G) (u : Chain) :
    baseContraction.proj (FreeCE.constantAction x u) =
      positiveTensorAction PositiveCE.Harmonic x (baseContraction.proj u) := by
  have hp (v : Cochain) : PositiveCE.harmonicProjection (ColorRoot.positiveAction x v) =
      ⁅x, PositiveCE.harmonicProjection v⁆ :=
    Subtype.ext (PositiveCE.harmonicProjection_positiveAction x v)
  induction u using TensorProduct.inductionOn with
  | tmul a v =>
    simp only [positiveTensorAction_tmul, FreeCE.constantAction_tmul, map_add,
      baseContraction_proj_tmul, hp]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The original tensor homotopy intertwines the actual diagonal constant action. -/
theorem base_homotopy_constantAction (x : G) (u : Chain) :
    baseContraction.homotopy (FreeCE.constantAction x u) =
      FreeCE.constantAction x (baseContraction.homotopy u) := by
  have hh (v : Cochain) : PositiveCE.chainContraction.homotopy (ColorRoot.positiveAction x v) =
      ColorRoot.positiveAction x (PositiveCE.chainContraction.homotopy v) :=
    PositiveCE.homotopyLie.map_lie x v
  induction u using TensorProduct.inductionOn with
  | tmul a v =>
    simp only [FreeCE.constantAction_tmul, map_add, baseContraction_homotopy_tmul, hh]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The finite perturbation series is equivariant for the actual constant sl₂ action. -/
theorem series_constantAction (x : G) (u : Chain) :
    series (FreeCE.constantAction x u) = FreeCE.constantAction x (series u) := by
  exact (Perturbation.series_commute baseContraction FreeCE.action
    (FreeCE.constantAction x).toAddMonoidHom
    (fun v => (base_homotopy_constantAction x v).symm)
    (fun v => (FreeCE.action_constantAction x v).symm)
    isUnit_one_add_action_homotopy u).symm

/-- The actual transferred differential is constant-sl₂ equivariant. -/
theorem differential_constantAction (x : G) (u : HarmonicChain) :
    differential (positiveTensorAction PositiveCE.Harmonic x u) =
      positiveTensorAction PositiveCE.Harmonic x (differential u) := by
  simp only [differential_apply, base_incl_constantAction, series_constantAction,
    base_proj_constantAction]

/-- The actual perturbed inclusion is equivariant. -/
theorem contraction_incl_constantAction (x : G) (u : HarmonicChain) :
    contraction.incl (positiveTensorAction PositiveCE.Harmonic x u) =
      FreeCE.constantAction x (contraction.incl u) := by
  simp only [contraction_incl_apply, base_incl_constantAction, series_constantAction,
    base_homotopy_constantAction, map_sub]

/-- The actual perturbed projection is equivariant. -/
theorem contraction_proj_constantAction (x : G) (u : Chain) :
    contraction.proj (FreeCE.constantAction x u) =
      positiveTensorAction PositiveCE.Harmonic x (contraction.proj u) := by
  simp only [contraction_proj_apply, base_proj_constantAction, series_constantAction,
    base_homotopy_constantAction, map_sub]

/-- The actual perturbed homotopy is equivariant. -/
theorem contraction_homotopy_constantAction (x : G) (u : Chain) :
    contraction.homotopy (FreeCE.constantAction x u) =
      FreeCE.constantAction x (contraction.homotopy u) := by
  simp only [contraction_homotopy_apply, base_homotopy_constantAction, series_constantAction, map_sub]

/-- The actual transferred differential as a morphism of constant sl₂ modules. -/
def differentialLie : HarmonicChain →ₗ⁅ℂ,G⁆ HarmonicChain :=
  { differential.restrictScalars ℂ with map_lie' := fun {x u} => differential_constantAction x u }

/-- The perturbed inclusion as a morphism of constant sl₂ modules. -/
def inclusionLie : HarmonicChain →ₗ⁅ℂ,G⁆ Chain :=
  { contraction.incl.restrictScalars ℂ with map_lie' := fun {x u} => contraction_incl_constantAction x u }

/-- The perturbed projection as a morphism of constant sl₂ modules. -/
def projectionLie : Chain →ₗ⁅ℂ,G⁆ HarmonicChain :=
  { contraction.proj.restrictScalars ℂ with map_lie' := fun {x u} => contraction_proj_constantAction x u }

/-- The perturbed homotopy as a morphism of constant sl₂ modules. -/
def homotopyLie : Chain →ₗ⁅ℂ,G⁆ Chain :=
  { contraction.homotopy.restrictScalars ℂ with
    map_lie' := fun {x u} => contraction_homotopy_constantAction x u }

end KhanSL2.BGG.PositiveTransfer
