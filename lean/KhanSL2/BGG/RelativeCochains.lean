module

public import KhanSL2.BGG.RelativeCochainsBasic
public import KhanSL2.BGG.FreeCEEquivariance
public import KhanSL2.BGG.FreeCESquareZero

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Actual relative CE cochain differential, and its ordinary coefficient formula. -/
noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.BGG.RelativeCochains
open scoped RelativeCochains

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [LieRingModule G V] [LieModule ℂ G V]
  [AddCommGroup W] [Module ℂ W] [LieRingModule G W] [LieModule ℂ G W]

@[ext] theorem tensorHom_ext {f g : tensorHom M V}
    (h : ∀ t, f.val t = g.val t) : f = g :=
  Subtype.ext (LinearMap.ext h)

/-- Precomposition by an actual positive-linear, constant-equivariant tensor map. -/
def precompose (F : (PositiveEnveloping ⊗[ℂ] V) →ₗ[PositiveEnveloping]
    (PositiveEnveloping ⊗[ℂ] W))
    (hF : ∀ x t, F (positiveTensorAction V x t) = positiveTensorAction W x (F t)) :
    tensorHom M W →ₗ[ℂ] tensorHom M V where
  toFun f := ⟨f.val.comp F, by
    intro x t
    change f.val (F (positiveTensorAction V x t)) = _
    rw [hF, f.property]
    rfl⟩
  map_add' f g := tensorHom_ext M (fun _ => rfl)
  map_smul' r f := tensorHom_ext M (fun _ => rfl)

@[simp] theorem precompose_apply
    (F : (PositiveEnveloping ⊗[ℂ] V) →ₗ[PositiveEnveloping]
      (PositiveEnveloping ⊗[ℂ] W))
    (hF : ∀ x t, F (positiveTensorAction V x t) = positiveTensorAction W x (F t))
    (f : tensorHom M W) (t : PositiveEnveloping ⊗[ℂ] V) :
    (precompose M F hF f).val t = f.val (F t) := rfl

/-- The actual free relative Hom model. -/
abbrev FreeHom := tensorHom M PositiveCE.Cochain

/-- Ordinary complex-linear, constant-equivariant relative cochains. -/
abbrev Ordinary := coefficientHom M PositiveCE.Cochain

/-- The relative cochain differential is precomposition by the actual free CE boundary. -/
def differential : Module.End ℂ (FreeHom M) :=
  precompose M FreeCE.differential FreeCE.differential_constantAction

@[simp] theorem differential_apply (f : FreeHom M) (t : FreeCE.Chain) :
    (differential M f).val t = f.val (FreeCE.differential t) := rfl

@[simp] theorem differential_square_zero (f : FreeHom M) :
    differential M (differential M f) = 0 := by
  apply tensorHom_ext M
  intro t
  simp only [differential_apply, FreeCE.differential_square_zero, map_zero,
    Submodule.coe_zero, LinearMap.zero_apply]

/-- The relative CE differential in the ordinary coefficient model. -/
def ordinaryDifferential : Module.End ℂ (Ordinary M) :=
  (tensorHomEquiv M PositiveCE.Cochain).toLinearMap.comp
    ((differential M).comp (tensorHomEquiv M PositiveCE.Cochain).symm.toLinearMap)

@[simp] theorem ordinaryDifferential_apply (f : Ordinary M) (ω : PositiveCE.Cochain) :
    (ordinaryDifferential M f).val ω =
      ((tensorHomEquiv M PositiveCE.Cochain).symm f).val
        (FreeCE.differential (1 ⊗ₜ[ℂ] ω)) := rfl

@[simp] theorem ordinaryDifferential_square_zero (f : Ordinary M) :
    ordinaryDifferential M (ordinaryDifferential M f) = 0 := by
  let e := tensorHomEquiv M PositiveCE.Cochain
  change e (differential M (e.symm (e (differential M (e.symm f))))) = 0
  calc
    _ = e (differential M (differential M (e.symm f))) :=
      congrArg (fun z => e (differential M z)) (e.symm_apply_apply (differential M (e.symm f)))
    _ = e 0 := congrArg e (differential_square_zero M (e.symm f))
    _ = 0 := e.map_zero
/-- The ordinary differential has exactly the finite CE action-plus-bracket formula. -/
theorem ordinaryDifferential_finite (f : Ordinary M) (ω : PositiveCE.Cochain)
    (S : Finset PositiveCE.Mode) (hω : FiniteExterior.supportModes ω ⊆ S) :
    (ordinaryDifferential M f).val ω =
      (∑ m∈S, positiveFactor (FreeCE.ueGenerator m) • f.val (PositiveCE.contract m ω)) +
        f.val (PositiveCE.boundary ω) := by
  rw [ordinaryDifferential_apply, FreeCE.differential_tmul_finite S 1 ω hω,
    map_add, map_sum]
  simp only [tensorHomEquiv_symm_tmul, one_mul, map_one, one_smul]

/-- Evaluation intertwines the specified differentials, so this is an equivalence of complexes. -/
theorem tensorHomEquiv_differential (f : FreeHom M) :
    tensorHomEquiv M PositiveCE.Cochain (differential M f) =
      ordinaryDifferential M (tensorHomEquiv M PositiveCE.Cochain f) := by
  let e := tensorHomEquiv M PositiveCE.Cochain
  exact (congrArg (fun z => e (differential M z)) (e.symm_apply_apply f)).symm
end KhanSL2.BGG.RelativeCochains
