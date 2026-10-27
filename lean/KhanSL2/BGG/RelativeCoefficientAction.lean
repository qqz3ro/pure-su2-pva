module

public import KhanSL2.BGG.RelativeCochainsBasic
public import Mathlib.Algebra.Algebra.Tower

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The actual constant representation on any current-enveloping coefficient module. -/
noncomputable section
namespace KhanSL2.BGG.RelativeCochains
attribute [local instance 100] LieRing.ofAssociativeRing

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]

/-- Restrict the actual enveloping action along the inclusion of constant matrices. -/
def coefficientConstantAction : G →ₗ⁅ℂ⁆ Module.End ℂ M :=
  (Algebra.lsmul ℂ ℂ M).toLieHom.comp ((UniversalEnvelopingAlgebra.ι ℂ).comp constant)

@[simp] theorem coefficientConstantAction_apply (x : G) (m : M) :
    coefficientConstantAction M x m = constGenerator x • m := rfl

scoped instance constantLieRingModule : LieRingModule G M :=
  LieRingModule.compLieHom M (coefficientConstantAction M)

scoped instance constantLieModule : LieModule ℂ G M :=
  LieModule.compLieHom M (coefficientConstantAction M)

@[simp] theorem coefficient_lie (x : G) (m : M) : ⁅x,m⁆ = constGenerator x • m := rfl

variable (V : Type*) [AddCommGroup V] [Module ℂ V]
  [LieRingModule G V] [LieModule ℂ G V]

/-- The concrete intertwining condition is exactly the bundled Hom-g space. -/
def coefficientHomLieEquiv : coefficientHom M V ≃ₗ[ℂ] (V →ₗ⁅ℂ,G⁆ M) where
  toFun f := { f.val with map_lie' := fun {x v} => f.property x v }
  invFun f := ⟨f.toLinearMap, fun x v => f.map_lie x v⟩
  left_inv f := by apply Subtype.ext; rfl
  right_inv f := by apply LieModuleHom.ext; intro v; rfl
  map_add' f g := by apply LieModuleHom.ext; intro v; rfl
  map_smul' r f := by apply LieModuleHom.ext; intro v; rfl

omit [LieModule ℂ G V] in
@[simp] theorem coefficientHomLieEquiv_apply (f : coefficientHom M V) (v : V) :
    coefficientHomLieEquiv M V f v = f.val v := rfl

omit [LieModule ℂ G V] in
@[simp] theorem coefficientHomLieEquiv_symm_apply (f : V →ₗ⁅ℂ,G⁆ M) (v : V) :
    ((coefficientHomLieEquiv M V).symm f).val v = f v := rfl

end KhanSL2.BGG.RelativeCochains
