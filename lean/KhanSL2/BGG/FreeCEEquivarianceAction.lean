module

public import KhanSL2.BGG.FreeCE
public import KhanSL2.BGG.TermPBWAction
public import KhanSL2.BGG.PositiveBoundaryEquivariance
public import Mathlib.Algebra.Lie.TensorProduct

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The actual constant-sl₂ action on the positive enveloping algebra and free CE tensors. -/
noncomputable section
open scoped BigOperators TensorProduct
namespace KhanSL2.BGG
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Constants act on the positive ideal by actual Lie derivations. -/
def positiveConstantDerivationHom : G →ₗ⁅ℂ⁆ LieDerivation ℂ positive positive where
  toFun := positiveConstantDerivation
  map_add' x y := by
    apply LieDerivation.ext
    intro u
    apply Subtype.ext
    rw [LieDerivation.add_apply]
    simp only [LieSubmodule.coe_add, positiveConstantDerivation_coe]
    change ⁅constant (x+y), (u : Current)⁆ =
      ⁅constant x, (u : Current)⁆ + ⁅constant y, (u : Current)⁆
    rw [map_add, LieRing.add_lie]
  map_smul' r x := by
    apply LieDerivation.ext
    intro u
    apply Subtype.ext
    rw [LieDerivation.smul_apply]
    simp only [RingHom.id_apply, LieSubmodule.coe_smul, positiveConstantDerivation_coe]
    change ⁅constant (r • x), (u : Current)⁆ = r • ⁅constant x, (u : Current)⁆
    rw [map_smul, ← lie_skew, LieAlgebra.lie_smul r (u : Current) (constant x), ← lie_skew (constant x) (u : Current), smul_neg]
  map_lie' := by
    intro x y
    apply LieDerivation.ext
    intro u
    apply Subtype.ext
    rw [LieDerivation.lie_apply]
    simp only [LieSubmodule.coe_sub, positiveConstantDerivation_coe]
    change ⁅constant ⁅x,y⁆, (u : Current)⁆ =
      ⁅constant x, ⁅constant y, (u : Current)⁆⁆ -
        ⁅constant y, ⁅constant x, (u : Current)⁆⁆
    rw [LieHom.map_lie, LieRing.leibniz_lie, add_sub_cancel_right]

/-- The extension of that action to the actual enveloping algebra, as a proved Lie representation. -/
def positiveUEAction : G →ₗ⁅ℂ⁆ Module.End ℂ PositiveEnveloping :=
  (TauCeti.derivationLieAlgebra ℂ PositiveEnveloping).incl.comp
    ((TauCeti.UniversalEnvelopingAlgebra.envelopingDerivationHom ℂ positive).comp
      positiveConstantDerivationHom)

@[simp] theorem positiveUEAction_apply (x : G) (u : PositiveEnveloping) :
    positiveUEAction x u = (positiveUEDerivation x : Module.End ℂ PositiveEnveloping) u := by
  change ((TauCeti.UniversalEnvelopingAlgebra.envelopingDerivationHom ℂ positive)
    (positiveConstantDerivationHom x) : Module.End ℂ PositiveEnveloping) u = _
  rw [show positiveConstantDerivationHom x = positiveConstantDerivation x from rfl,
    TauCeti.UniversalEnvelopingAlgebra.envelopingDerivationHom_apply]
  rfl
instance positiveUE_lieRingModule : LieRingModule G PositiveEnveloping :=
  LieRingModule.compLieHom PositiveEnveloping positiveUEAction

instance positiveUE_lieModule : LieModule ℂ G PositiveEnveloping :=
  LieModule.compLieHom PositiveEnveloping positiveUEAction

@[simp] theorem positiveUE_lie (x : G) (u : PositiveEnveloping) :
    ⁅x,u⁆ = (positiveUEDerivation x : Module.End ℂ PositiveEnveloping) u := by
  change positiveUEAction x u = _
  exact positiveUEAction_apply x u
theorem positiveUEAction_mul (x : G) (u v : PositiveEnveloping) :
    positiveUEAction x (u*v) = positiveUEAction x u*v + u*positiveUEAction x v :=
  by simpa only [positiveUEAction_apply] using
    TauCeti.derivationLieAlgebra.leibniz (positiveUEDerivation x) u v

/-- Any constant representation tensored with U(n) carries the canonical diagonal action. -/
def positiveTensorAction (M : Type*) [AddCommGroup M] [Module ℂ M]
    [LieRingModule G M] [LieModule ℂ G M] :
    G →ₗ⁅ℂ⁆ Module.End ℂ (PositiveEnveloping ⊗[ℂ] M) := LieModule.toEnd ℂ G _

@[simp] theorem positiveTensorAction_tmul (M : Type*) [AddCommGroup M] [Module ℂ M]
    [LieRingModule G M] [LieModule ℂ G M] (x : G) (u : PositiveEnveloping) (m : M) :
    positiveTensorAction M x (u ⊗ₜ[ℂ] m) =
      positiveUEAction x u ⊗ₜ[ℂ] m + u ⊗ₜ[ℂ] ⁅x,m⁆ :=
  TensorProduct.LieModule.lie_tmul_right x u m

end KhanSL2.BGG

namespace KhanSL2.BGG.FreeCE
open PositiveCE FiniteExterior
attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual diagonal constant action on the free Chevalley--Eilenberg module. -/
def constantAction : G →ₗ⁅ℂ⁆ Module.End ℂ Chain := positiveTensorAction Cochain

@[simp] theorem constantAction_tmul (x : G) (u : PositiveEnveloping) (ω : Cochain) :
    constantAction x (u ⊗ₜ[ℂ] ω) =
      positiveUEAction x u ⊗ₜ[ℂ] ω + u ⊗ₜ[ℂ] ColorRoot.positiveAction x ω :=
  positiveTensorAction_tmul Cochain x u ω

@[simp] theorem constantAction_color_tmul (a : Fin 3) (u : PositiveEnveloping) (ω : Cochain) :
    constantAction (MatrixSL2.color a) (u ⊗ₜ[ℂ] ω) =
      positiveUEAction (MatrixSL2.color a) u ⊗ₜ[ℂ] ω + u ⊗ₜ[ℂ] PositiveCE.colorAction a ω := by
  rw [constantAction_tmul, ColorRoot.positiveAction_color]

/-- The concrete color action on the actual positive-current basis. -/
theorem positiveConstantDerivation_color (a : Fin 3) (m : Mode) :
    positiveConstantDerivation (MatrixSL2.color a) (lieGenerator m) =
      ∑ c : Fin 3, KhanSL2.epsilon a m.color c • lieGenerator (⟨m.index,c⟩ : Mode) := by
  apply Subtype.ext
  rw [positiveConstantDerivation_coe]
  change ⁅constant (MatrixSL2.color a), mode (m.index+1) (MatrixSL2.color m.color)⁆ = _
  rw [constant_apply, mode_lie, Nat.zero_add, MatrixSL2.color_bracket]
  simp only [Fin.sum_univ_succ, map_add, map_smul, LieSubmodule.coe_add,
    LieSubmodule.coe_smul, lieGenerator, positiveMode_coe, Fin.sum_univ_zero, map_zero,
    LieSubmodule.coe_zero, add_zero]
/-- Deriving an actual enveloping generator has exactly the same color matrix. -/
theorem positiveUEAction_generator_color (a : Fin 3) (m : Mode) :
    positiveUEAction (MatrixSL2.color a) (ueGenerator m) =
      ∑ c : Fin 3, KhanSL2.epsilon a m.color c • ueGenerator (⟨m.index,c⟩ : Mode) := by
  rw [positiveUEAction_apply]
  change (TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation ℂ positive
      (positiveConstantDerivation (MatrixSL2.color a)) : Module.End ℂ PositiveEnveloping)
    (UniversalEnvelopingAlgebra.ι ℂ (lieGenerator m)) = _
  rw [TauCeti.UniversalEnvelopingAlgebra.envelopingDerivation_ι,
    positiveConstantDerivation_color, map_sum]
  simp only [map_smul, ueGenerator]

end KhanSL2.BGG.FreeCE
