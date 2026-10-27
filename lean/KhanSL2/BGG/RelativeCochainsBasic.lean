module

public import KhanSL2.BGG.FreeCEEquivarianceAction

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Relative tensor Hom and actual equivariant coefficient cochains. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.BGG.RelativeCochains

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]

/-- Restrict an actual current-enveloping module along the actual positive inclusion. -/
scoped instance positiveModule : Module PositiveEnveloping M :=
  Module.compHom M positiveFactor.toRingHom

omit [Module ℂ M] [IsScalarTower ℂ Enveloping M] in
@[simp] theorem positive_smul (u : PositiveEnveloping) (m : M) :
    u • m = positiveFactor u • m := rfl

scoped instance positiveScalarTower : IsScalarTower ℂ PositiveEnveloping M where
  smul_assoc r u m := by
    change positiveFactor (r • u) • m = r • (positiveFactor u • m)
    rw [map_smul, smul_assoc]

open scoped RelativeCochains

variable (V : Type*) [AddCommGroup V] [Module ℂ V]
  [LieRingModule G V] [LieModule ℂ G V]

/-- Ordinary coefficient cochains: actual complex-linear maps intertwining constants. -/
def coefficientHom : Submodule ℂ (V →ₗ[ℂ] M) where
  carrier := {f | ∀ (x : G) (v : V), f ⁅x,v⁆ = constGenerator x • f v}
  zero_mem' := by intro x v; simp
  add_mem' := by
    intro f g hf hg x v
    simp only [LinearMap.add_apply, hf x v, hg x v, smul_add]
  smul_mem' := by
    intro r f hf x v
    simp only [LinearMap.smul_apply, hf x v]
    exact smul_comm _ _ _

/-- Relative free cochains: positive-linear maps intertwining the diagonal constant action. -/
def tensorHom : Submodule ℂ ((PositiveEnveloping ⊗[ℂ] V) →ₗ[PositiveEnveloping] M) where
  carrier := {f | ∀ (x : G) (t : PositiveEnveloping ⊗[ℂ] V),
    f (positiveTensorAction V x t) = constGenerator x • f t}
  zero_mem' := by intro x t; simp
  add_mem' := by
    intro f g hf hg x t
    simp only [LinearMap.add_apply, hf x t, hg x t, smul_add]
  smul_mem' := by
    intro r f hf x t
    simp only [LinearMap.smul_apply, hf x t]
    exact smul_comm _ _ _

@[simp] theorem positiveTensorAction_one_tmul (x : G) (v : V) :
    positiveTensorAction V x ((1 : PositiveEnveloping) ⊗ₜ[ℂ] v) =
      (1 : PositiveEnveloping) ⊗ₜ[ℂ] ⁅x,v⁆ := by
  rw [positiveTensorAction_tmul, positiveUEAction_apply,
    TauCeti.derivationLieAlgebra.apply_one_eq_zero, TensorProduct.zero_tmul, zero_add]

/-- Evaluation at the scalar enveloping generator. -/
def evaluate : tensorHom M V →ₗ[ℂ] coefficientHom M V where
  toFun f := ⟨((f.val).restrictScalars ℂ).comp (TensorProduct.mk ℂ PositiveEnveloping V 1), by
    intro x v
    change f.val (1 ⊗ₜ[ℂ] ⁅x,v⁆) = constGenerator x • f.val (1 ⊗ₜ[ℂ] v)
    rw [← positiveTensorAction_one_tmul]
    exact f.property x (1 ⊗ₜ[ℂ] v)⟩
  map_add' f g := by apply Subtype.ext; apply LinearMap.ext; intro v; rfl
  map_smul' r f := by apply Subtype.ext; apply LinearMap.ext; intro v; rfl

@[simp] theorem evaluate_apply (f : tensorHom M V) (v : V) :
    (evaluate M V f).val v = f.val (1 ⊗ₜ[ℂ] v) := rfl

/-- The actual tensor extension is constant-equivariant, by the commutator formula in U(g[x]). -/
theorem tensorLift_equivariant (f : coefficientHom M V) (x : G)
    (t : PositiveEnveloping ⊗[ℂ] V) :
    Induced.tensorLift f.val (positiveTensorAction V x t) =
      constGenerator x • Induced.tensorLift f.val t := by
  induction t using TensorProduct.inductionOn with
  | tmul u v =>
    rw [positiveTensorAction_tmul, map_add, Induced.tensorLift_tmul,
      Induced.tensorLift_tmul, Induced.tensorLift_tmul, f.property,
      positive_smul, positive_smul, positive_smul,
      positiveUEAction_apply, positiveFactor_derivation, sub_smul, mul_smul, mul_smul]
    abel
  | add t s ht hs => simp only [map_add, ht, hs, smul_add]

/-- Extension by the genuine positive enveloping action on the coefficients. -/
def extend : coefficientHom M V →ₗ[ℂ] tensorHom M V where
  toFun f := ⟨Induced.tensorLift f.val, tensorLift_equivariant M V f⟩
  map_add' f g := by
    apply Subtype.ext
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul u v => simp only [Submodule.coe_add, Induced.tensorLift_tmul, LinearMap.add_apply, smul_add]
    | add t s ht hs => simp only [map_add, LinearMap.add_apply, ht, hs]
  map_smul' r f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
      simp only [Submodule.coe_smul, Induced.tensorLift_tmul, LinearMap.smul_apply]
      exact smul_comm _ _ _
    | add t s ht hs => simp only [map_add, LinearMap.smul_apply, ht, hs, smul_add]

@[simp] theorem extend_tmul (f : coefficientHom M V) (u : PositiveEnveloping) (v : V) :
    (extend M V f).val (u ⊗ₜ[ℂ] v) = u • f.val v := rfl

/-- The ordinary relative coefficient model is linearly equivalent to the free relative Hom model. -/
def tensorHomEquiv : tensorHom M V ≃ₗ[ℂ] coefficientHom M V where
  toLinearMap := evaluate M V
  invFun := extend M V
  left_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
      change (extend M V (evaluate M V f)).val (u ⊗ₜ[ℂ] v) = _
      rw [extend_tmul, evaluate_apply]
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
        (f.val.map_smul u (1 ⊗ₜ[ℂ] v)).symm
    | add t s ht hs => simp only [map_add, ht, hs]
  right_inv f := by
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    change (evaluate M V (extend M V f)).val v = f.val v
    rw [evaluate_apply, extend_tmul, one_smul]

@[simp] theorem tensorHomEquiv_apply (f : tensorHom M V) (v : V) :
    (tensorHomEquiv M V f).val v = f.val (1 ⊗ₜ[ℂ] v) := rfl

@[simp] theorem tensorHomEquiv_symm_tmul (f : coefficientHom M V)
    (u : PositiveEnveloping) (v : V) :
    ((tensorHomEquiv M V).symm f).val (u ⊗ₜ[ℂ] v) = positiveFactor u • f.val v := rfl

end KhanSL2.BGG.RelativeCochains
