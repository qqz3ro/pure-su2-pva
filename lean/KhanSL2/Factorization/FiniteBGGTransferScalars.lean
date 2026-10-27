module

public import KhanSL2.Factorization.CoefficientChainMaps
public import KhanSL2.BGGBridge.CoefficientOps

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace KhanSL2.Factorization.BGGTransfer
open BGG BGGBridge SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M] [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]

abbrev HarmonicQuotient := HarmN M ⧸ relH M

def harmonicScalarRaw (r : R) : Module.End ℂ (HarmN M) :=
  LinearMap.lTensor PositiveCE.Harmonic (coefficientScalarLieHom R M r).toLinearMap

theorem harmonicScalarRaw_action (r : R) (x : G) (z : HarmN M) :
    harmonicScalarRaw R M r (actH M x z) = actH M x (harmonicScalarRaw R M r z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul v m =>
    simp only [harmonicScalarRaw,actH,diag_tmul,map_add,LinearMap.lTensor_tmul,
      LieModule.toEnd_apply_apply]
    exact congrArg (fun n => ⁅x,v⁆ ⊗ₜ[ℂ] ((coefficientScalarLieHom R M r).toLinearMap m) + v ⊗ₜ[ℂ] n)
      ((coefficientScalarLieHom R M r).map_lie (constant x) m)

def harmonicScalar (r : R) : Module.End ℂ (HarmonicQuotient M) :=
  (relH M).mapQ (relH M) (harmonicScalarRaw R M r)
    (le_comap_of_commute (actH M) (actH M) (harmonicScalarRaw R M r)
      (harmonicScalarRaw_action R M r))

@[simp] theorem harmonicScalar_mk (r : R) (z : HarmN M) :
    harmonicScalar R M r (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (harmonicScalarRaw R M r z) := rfl

/-- Original coefficient multiplication on harmonic constant coinvariants. -/
def harmonicAction : R →ₐ[ℂ] Module.End ℂ (HarmonicQuotient M) where
  toFun := harmonicScalar R M
  map_zero' := by
    apply Submodule.linearMap_qext
    apply TensorProduct.ext'
    intro h m
    change (Submodule.Quotient.mk (h ⊗ₜ[ℂ] ((0:R) • m)) : HarmonicQuotient M) = 0
    rw [zero_smul,TensorProduct.tmul_zero,Submodule.Quotient.mk_zero]
  map_one' := by
    apply Submodule.linearMap_qext
    apply TensorProduct.ext'
    intro h m
    change (Submodule.Quotient.mk (h ⊗ₜ[ℂ] ((1:R) • m)) : HarmonicQuotient M) = Submodule.Quotient.mk (h ⊗ₜ[ℂ] m)
    rw [one_smul]
  map_add' r t := by
    apply Submodule.linearMap_qext
    apply TensorProduct.ext'
    intro h m
    change (Submodule.Quotient.mk (h ⊗ₜ[ℂ] ((r+t) • m)) : HarmonicQuotient M) =
      Submodule.Quotient.mk (h ⊗ₜ[ℂ] (r • m)) + Submodule.Quotient.mk (h ⊗ₜ[ℂ] (t • m))
    rw [add_smul,TensorProduct.tmul_add,Submodule.Quotient.mk_add]
  map_mul' r t := by
    apply Submodule.linearMap_qext
    apply TensorProduct.ext'
    intro h m
    change (Submodule.Quotient.mk (h ⊗ₜ[ℂ] ((r*t) • m)) : HarmonicQuotient M) =
      Submodule.Quotient.mk (h ⊗ₜ[ℂ] (r • (t • m)))
    rw [mul_smul]
  commutes' c := by
    rw [show algebraMap ℂ (Module.End ℂ (HarmonicQuotient M)) c =
      c • (1 : Module.End ℂ (HarmonicQuotient M)) from Algebra.algebraMap_eq_smul_one c]
    apply Submodule.linearMap_qext
    apply TensorProduct.ext'
    intro h m
    change (Submodule.Quotient.mk (h ⊗ₜ[ℂ] (algebraMap ℂ R c • m)) : HarmonicQuotient M) =
      c • Submodule.Quotient.mk (h ⊗ₜ[ℂ] m)
    rw [IsScalarTower.algebraMap_smul,TensorProduct.tmul_smul,Submodule.Quotient.mk_smul]

@[instance_reducible] def harmonicModule : Module R (HarmonicQuotient M) :=
  Module.compHom (HarmonicQuotient M) (harmonicAction R M).toRingHom

attribute [local instance] harmonicModule coefficientChainModule

@[simp] theorem harmonic_smul (r : R) (z : HarmonicQuotient M) :
    r • z = harmonicScalar R M r z := rfl

theorem harmonicSMulCommClass : SMulCommClass ℂ R (HarmonicQuotient M) where
  smul_comm c r z := (map_smul (harmonicAction R M r) c z).symm

theorem harmonicIsScalarTower : IsScalarTower ℂ R (HarmonicQuotient M) where
  smul_assoc c r z := LinearMap.congr_fun ((harmonicAction R M).toLinearMap.map_smul c r) z

theorem scalar_ract (r : R) (u : PositiveEnveloping) (m : M) :
    coefficientScalarLieHom R M r (ract (rightAction M) u m) =
      ract (rightAction M) u (coefficientScalarLieHom R M r m) :=
  ract_commute M (fun y m => (coefficientScalarLieHom R M r).map_lie y m) u m

/-- The existing inclusion in the BGG contraction preserves the original scalars. -/
theorem incl_smul (r : R) (z : HarmonicQuotient M) :
    (qcN M).incl (r • z) = r • (qcN M).incl z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change Submodule.Quotient.mk ((cN M).incl (harmonicScalarRaw R M r z)) =
      Submodule.Quotient.mk (rawMap (coefficientScalarLieHom R M r).toLinearMap ((cN M).incl z))
    congr 1
    exact base_lTensor (rightAction M) (scalar_ract R M r) PositiveTransfer.contraction.incl z

/-- The existing projection in the BGG contraction preserves the original scalars. -/
theorem proj_smul (r : R) (z : RelativeChains M) :
    (qcN M).proj (r • z) = r • (qcN M).proj z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change Submodule.Quotient.mk ((cN M).proj
      (rawMap (coefficientScalarLieHom R M r).toLinearMap z)) =
      Submodule.Quotient.mk (harmonicScalarRaw R M r ((cN M).proj z))
    congr 1
    exact base_lTensor (rightAction M) (scalar_ract R M r) PositiveTransfer.contraction.proj z

/-- The existing contracting homotopy, not just the induced homology equivalence,
is linear for the original coefficient action. -/
theorem homotopy_smul (r : R) (z : RelativeChains M) :
    (qcN M).homotopy (r • z) = r • (qcN M).homotopy z := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    change Submodule.Quotient.mk ((cN M).homotopy
      (rawMap (coefficientScalarLieHom R M r).toLinearMap z)) =
      Submodule.Quotient.mk (rawMap (coefficientScalarLieHom R M r).toLinearMap ((cN M).homotopy z))
    congr 1
    exact base_lTensor (rightAction M) (scalar_ract R M r) PositiveTransfer.contraction.homotopy z

def inclLinear : HarmonicQuotient M →ₗ[R] RelativeChains M where
  __ := (qcN M).incl.toAddMonoidHom
  map_smul' := incl_smul R M

def projLinear : RelativeChains M →ₗ[R] HarmonicQuotient M where
  __ := (qcN M).proj.toAddMonoidHom
  map_smul' := proj_smul R M

def homotopyLinear : Module.End R (RelativeChains M) where
  __ := (qcN M).homotopy.toAddMonoidHom
  map_smul' := homotopy_smul R M

end KhanSL2.Factorization.BGGTransfer


