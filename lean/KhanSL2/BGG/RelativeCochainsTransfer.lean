module

public import KhanSL2.BGG.RelativeCochains
public import KhanSL2.BGG.PositiveTransferEquivariance

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The actual equivariant HPL maps give an explicit comparison on relative coefficient cochains. -/
noncomputable section
namespace KhanSL2.BGG.RelativeCochains
open scoped RelativeCochains

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]

/-- The full relative Hom complex on the actual transferred harmonic chains. -/
abbrev HarmonicHom := tensorHom M PositiveCE.Harmonic

/-- The harmonic Hom differential uses the specified transferred differential. -/
def harmonicDifferential : Module.End ℂ (HarmonicHom M) :=
  precompose M PositiveTransfer.differential PositiveTransfer.differential_constantAction

@[simp] theorem harmonicDifferential_apply (f : HarmonicHom M)
    (t : PositiveTransfer.HarmonicChain) :
    (harmonicDifferential M f).val t = f.val (PositiveTransfer.differential t) := rfl

@[simp] theorem harmonicDifferential_square_zero (f : HarmonicHom M) :
    harmonicDifferential M (harmonicDifferential M f) = 0 := by
  apply tensorHom_ext M
  intro t
  simp only [harmonicDifferential_apply, PositiveTransfer.differential_square_zero,
    map_zero, Submodule.coe_zero, LinearMap.zero_apply]

/-- Restriction along the genuine perturbed inclusion. -/
def toHarmonic : FreeHom M →ₗ[ℂ] HarmonicHom M :=
  precompose M PositiveTransfer.contraction.incl PositiveTransfer.contraction_incl_constantAction

/-- Extension along the genuine perturbed projection. -/
def fromHarmonic : HarmonicHom M →ₗ[ℂ] FreeHom M :=
  precompose M PositiveTransfer.contraction.proj PositiveTransfer.contraction_proj_constantAction

/-- The comparison homotopy is precomposition by the actual perturbed chain homotopy. -/
def comparisonHomotopy : Module.End ℂ (FreeHom M) :=
  precompose M PositiveTransfer.contraction.homotopy
    PositiveTransfer.contraction_homotopy_constantAction

@[simp] theorem toHarmonic_apply (f : FreeHom M) (t : PositiveTransfer.HarmonicChain) :
    (toHarmonic M f).val t = f.val (PositiveTransfer.contraction.incl t) := rfl

@[simp] theorem fromHarmonic_apply (f : HarmonicHom M) (t : FreeCE.Chain) :
    (fromHarmonic M f).val t = f.val (PositiveTransfer.contraction.proj t) := rfl

@[simp] theorem comparisonHomotopy_apply (f : FreeHom M) (t : FreeCE.Chain) :
    (comparisonHomotopy M f).val t = f.val (PositiveTransfer.contraction.homotopy t) := rfl

set_option maxHeartbeats 800000 in
/-- The full relative coefficient Hom complexes are related by an actual special contraction. -/
def comparison : TauCeti.LinearSpecialContraction (differential M) (harmonicDifferential M) where
  incl := fromHarmonic M
  proj := toHarmonic M
  homotopy := comparisonHomotopy M
  dM_comp_incl := by
    apply LinearMap.ext
    intro f
    apply tensorHom_ext M
    intro t
    change f.val (PositiveTransfer.contraction.proj (FreeCE.differential t)) =
      f.val (PositiveTransfer.differential (PositiveTransfer.contraction.proj t))
    exact congrArg f.val (LinearMap.congr_fun PositiveTransfer.contraction.proj_comp_dM t)
  proj_comp_dM := by
    apply LinearMap.ext
    intro f
    apply tensorHom_ext M
    intro t
    change f.val (FreeCE.differential (PositiveTransfer.contraction.incl t)) =
      f.val (PositiveTransfer.contraction.incl (PositiveTransfer.differential t))
    exact congrArg f.val (LinearMap.congr_fun PositiveTransfer.contraction.dM_comp_incl t)
  proj_comp_incl := by
    apply LinearMap.ext
    intro f
    apply tensorHom_ext M
    intro t
    change f.val (PositiveTransfer.contraction.proj (PositiveTransfer.contraction.incl t)) = f.val t
    exact congrArg f.val (LinearMap.congr_fun PositiveTransfer.contraction.proj_comp_incl t)
  dM_comp_homotopy_add_homotopy_comp_dM := by
    apply LinearMap.ext
    intro f
    apply tensorHom_ext M
    intro t
    change f.val (PositiveTransfer.contraction.homotopy (FreeCE.differential t)) +
      f.val (FreeCE.differential (PositiveTransfer.contraction.homotopy t)) =
      f.val t - f.val (PositiveTransfer.contraction.incl (PositiveTransfer.contraction.proj t))
    rw [← map_add, add_comm, PositiveTransfer.contraction_identity, map_sub]
  homotopy_comp_incl := by
    apply LinearMap.ext
    intro f
    apply tensorHom_ext M
    intro t
    change f.val (PositiveTransfer.contraction.proj (PositiveTransfer.contraction.homotopy t)) = 0
    rw [show PositiveTransfer.contraction.proj (PositiveTransfer.contraction.homotopy t) = 0 from
      LinearMap.congr_fun PositiveTransfer.contraction.proj_comp_homotopy t, map_zero]
  proj_comp_homotopy := by
    apply LinearMap.ext
    intro f
    apply tensorHom_ext M
    intro t
    change f.val (PositiveTransfer.contraction.homotopy (PositiveTransfer.contraction.incl t)) = 0
    rw [show PositiveTransfer.contraction.homotopy (PositiveTransfer.contraction.incl t) = 0 from
      LinearMap.congr_fun PositiveTransfer.contraction.homotopy_comp_incl t, map_zero]
  homotopy_comp_homotopy := by
    apply LinearMap.ext
    intro f
    apply tensorHom_ext M
    intro t
    change f.val (PositiveTransfer.contraction.homotopy (PositiveTransfer.contraction.homotopy t)) = 0
    rw [show PositiveTransfer.contraction.homotopy (PositiveTransfer.contraction.homotopy t) = 0 from
      LinearMap.congr_fun PositiveTransfer.contraction.homotopy_comp_homotopy t, map_zero]

/-- Explicit cochain homotopy identity, using the same concrete comparison maps. -/
theorem comparison_identity (f : FreeHom M) :
    differential M (comparisonHomotopy M f) + comparisonHomotopy M (differential M f) =
      f - fromHarmonic M (toHarmonic M f) :=
  LinearMap.congr_fun (comparison M).dM_comp_homotopy_add_homotopy_comp_dM f

end KhanSL2.BGG.RelativeCochains
