module

public import KhanSL2.Factorization.CoefficientTotalFunctor
public import KhanSL2.SymmetricFamily.CoefficientBaseChange

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The original coefficient ring acts on actual relative homology through
its original scalar endomorphisms of the coefficient current module. -/
noncomputable section
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
  [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]

/-- Scalar multiplication in the given coefficient module, as an actual current map. -/
def coefficientScalarLieHom (r : R) : M →ₗ⁅ℂ,Current⁆ M where
  toFun m := r • m
  map_add' m n := smul_add r m n
  map_smul' c m := smul_comm r c m
  map_lie' {x m} := (CoefficientLinearCurrent.lie_smul x r m).symm

omit [LieModule ℂ Current M] in
@[simp] theorem coefficientScalarLieHom_apply (r : R) (m : M) :
    coefficientScalarLieHom R M r m = r • m := rfl

omit [LieModule ℂ Current M] in
@[simp] theorem coefficientScalarLieHom_zero :
    coefficientScalarLieHom R M 0 = 0 := by ext m; exact zero_smul R m

omit [LieModule ℂ Current M] in
@[simp] theorem coefficientScalarLieHom_one :
    coefficientScalarLieHom R M 1 = LieModuleHom.id := by ext m; exact one_smul R m

omit [LieModule ℂ Current M] in
theorem coefficientScalarLieHom_add (r t : R) :
    coefficientScalarLieHom R M (r+t) = coefficientScalarLieHom R M r + coefficientScalarLieHom R M t := by
  ext m
  exact add_smul r t m

omit [LieModule ℂ Current M] in
theorem coefficientScalarLieHom_mul (r t : R) :
    coefficientScalarLieHom R M (r*t) =
      (coefficientScalarLieHom R M r).comp (coefficientScalarLieHom R M t) := by
  ext m
  exact mul_smul r t m

theorem coefficientScalarLieHom_algebraMap (c : ℂ) :
    coefficientScalarLieHom R M (algebraMap ℂ R c) = c • (LieModuleHom.id : M →ₗ⁅ℂ,Current⁆ M) := by
  ext m
  exact IsScalarTower.algebraMap_smul R c m

/-- The coefficient algebra acts by the induced original scalar maps on cycle classes. -/
def coefficientTotalHomologyAction : R →ₐ[ℂ] Module.End ℂ (TotalHomology M) where
  toFun r := coefficientTotalHomologyMap (coefficientScalarLieHom R M r)
  map_zero' := by rw [coefficientScalarLieHom_zero,coefficientTotalHomologyMap_zero]
  map_one' := by rw [coefficientScalarLieHom_one,coefficientTotalHomologyMap_id]; rfl
  map_add' r t := by rw [coefficientScalarLieHom_add,coefficientTotalHomologyMap_add]
  map_mul' r t := by rw [coefficientScalarLieHom_mul,coefficientTotalHomologyMap_comp]; rfl
  commutes' c := by
    rw [coefficientScalarLieHom_algebraMap,coefficientTotalHomologyMap_smul,
      coefficientTotalHomologyMap_id,Algebra.algebraMap_eq_smul_one]
    rfl

/-- The original coefficient action on actual homology, not a transported root action. -/
@[instance_reducible] def coefficientTotalHomologyModule : Module R (TotalHomology M) :=
  Module.compHom (TotalHomology M) (coefficientTotalHomologyAction R M).toRingHom

attribute [local instance] coefficientTotalHomologyModule

@[simp] theorem coefficientTotalHomology_smul (r : R) (u : TotalHomology M) :
    r • u = coefficientTotalHomologyMap (coefficientScalarLieHom R M r) u := rfl

theorem coefficientTotalHomologySMulCommClass : SMulCommClass ℂ R (TotalHomology M) where
  smul_comm c r u := (map_smul (coefficientTotalHomologyAction R M r) c u).symm

theorem coefficientTotalHomologyIsScalarTower : IsScalarTower ℂ R (TotalHomology M) where
  smul_assoc c r u :=
    LinearMap.congr_fun ((coefficientTotalHomologyAction R M).toLinearMap.map_smul c r) u

end KhanSL2.Factorization
