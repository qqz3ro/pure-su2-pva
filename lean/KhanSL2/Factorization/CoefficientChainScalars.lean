module

public import KhanSL2.Factorization.CoefficientTotalScalars
public import KhanSL2.Factorization.RelativeChainsComplex

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The genuine coefficient action on the actual relative CE chain groups,
with the original degree groups and differential retained over the coefficient ring. -/
noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
  [LieRingModule Current M] [LieModule ℂ Current M]
  [CoefficientLinearCurrent R M]

/-- Original coefficient scalars on the actual constant-coinvariant CE chains. -/
def coefficientChainAction : R →ₐ[ℂ] Module.End ℂ (RelativeChains M) where
  toFun r := coefficientMap (coefficientScalarLieHom R M r).toLinearMap
    (constantEquivariant_of_lieHom (coefficientScalarLieHom R M r))
  map_zero' := by rw [coefficientScalarLieHom_zero]; exact coefficientMap_zero
  map_one' := by rw [coefficientScalarLieHom_one]; exact coefficientMap_id
  map_add' r t := by
    rw [coefficientScalarLieHom_add]
    exact coefficientMap_add _ _ _ _
  map_mul' r t := by
    rw [coefficientScalarLieHom_mul]
    exact coefficientMap_comp _ _ _ _
  commutes' c := by
    rw [coefficientScalarLieHom_algebraMap]
    change coefficientMap (c • (LinearMap.id : M →ₗ[ℂ] M)) _ = _
    rw [coefficientMap_smul c LinearMap.id ConstantEquivariant.id,
      coefficientMap_id,Algebra.algebraMap_eq_smul_one]
    rfl

@[instance_reducible] def coefficientChainModule : Module R (RelativeChains M) :=
  Module.compHom (RelativeChains M) (coefficientChainAction R M).toRingHom

attribute [local instance] coefficientChainModule

@[simp] theorem coefficientChain_smul (r : R) (z : RelativeChains M) :
    r • z = coefficientMap (coefficientScalarLieHom R M r).toLinearMap
      (constantEquivariant_of_lieHom (coefficientScalarLieHom R M r)) z := rfl

/-- This action literally multiplies the original coefficient tensor factor. -/
theorem coefficientChain_smul_mk_tmul (r : R) (ω : BGG.PositiveCE.Cochain) (m : M) :
    r • (Submodule.Quotient.mk (ω ⊗ₜ[ℂ] m) : RelativeChains M) =
      Submodule.Quotient.mk (ω ⊗ₜ[ℂ] (r • m)) := rfl

theorem coefficientChainSMulCommClass : SMulCommClass ℂ R (RelativeChains M) where
  smul_comm c r z := (map_smul (coefficientChainAction R M r) c z).symm

theorem coefficientChainIsScalarTower : IsScalarTower ℂ R (RelativeChains M) where
  smul_assoc c r z := LinearMap.congr_fun
    ((coefficientChainAction R M).toLinearMap.map_smul c r) z

/-- The original CE boundary is coefficient-linear. -/
theorem differential_coefficient_smul (r : R) (z : RelativeChains M) :
    differential M (r • z) = r • differential M z :=
  (coefficientMap_differential (coefficientScalarLieHom R M r) z).symm

/-- The same actual boundary, bundled over the original coefficient ring. -/
def coefficientDifferentialLinear : Module.End R (RelativeChains M) where
  __ := (differential M).toAddMonoidHom
  map_smul' := differential_coefficient_smul R M

/-- Restrict original scalar maps to each unchanged exterior-degree group. -/
def coefficientDegreeAction (j : ℕ) : R →ₐ[ℂ] Module.End ℂ (degree M j) where
  toFun r := coefficientDegreeMap (coefficientScalarLieHom R M r).toLinearMap
    (constantEquivariant_of_lieHom (coefficientScalarLieHom R M r)) j
  map_zero' := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    exact LinearMap.congr_fun (map_zero (coefficientChainAction R M)) z.val
  map_one' := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    exact LinearMap.congr_fun (map_one (coefficientChainAction R M)) z.val
  map_add' r t := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    exact LinearMap.congr_fun (map_add (coefficientChainAction R M) r t) z.val
  map_mul' r t := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    exact LinearMap.congr_fun (map_mul (coefficientChainAction R M) r t) z.val
  commutes' c := by
    apply LinearMap.ext; intro z; apply Subtype.ext
    exact LinearMap.congr_fun ((coefficientChainAction R M).commutes c) z.val

@[instance_reducible] def coefficientDegreeModule (j : ℕ) : Module R (degree M j) :=
  Module.compHom (degree M j) (coefficientDegreeAction R M j).toRingHom

attribute [local instance] coefficientDegreeModule

@[simp] theorem coefficientDegree_smul_val (j : ℕ) (r : R) (z : degree M j) :
    (r • z : degree M j).val = r • z.val := rfl

theorem coefficientDegreeSMulCommClass (j : ℕ) : SMulCommClass ℂ R (degree M j) where
  smul_comm c r z := (map_smul (coefficientDegreeAction R M j r) c z).symm

theorem coefficientDegreeIsScalarTower (j : ℕ) : IsScalarTower ℂ R (degree M j) where
  smul_assoc c r z := LinearMap.congr_fun
    ((coefficientDegreeAction R M j).toLinearMap.map_smul c r) z

/-- The actual degree-lowering CE differential over the coefficient ring. -/
def coefficientDegreeDifferentialLinear (j : ℕ) : degree M (j+1) →ₗ[R] degree M j where
  __ := (degreeDifferential M j).toAddMonoidHom
  map_smul' r z := Subtype.ext (differential_coefficient_smul R M r z.val)

/-- The original relative complex, now over its original coefficient ring. -/
def coefficientRelativeComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun j => ModuleCat.of R (degree M j))
    (fun j => ModuleCat.ofHom (coefficientDegreeDifferentialLinear R M j)) (fun j => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact LinearMap.congr_fun (differential_comp_self M) z.val)

@[simp] theorem coefficientRelativeComplex_X (j : ℕ) :
    (coefficientRelativeComplex R M).X j = ModuleCat.of R (degree M j) := rfl

@[simp] theorem coefficientRelativeComplex_d (j : ℕ) :
    (coefficientRelativeComplex R M).d (j+1) j =
      ModuleCat.ofHom (coefficientDegreeDifferentialLinear R M j) := by
  simp only [coefficientRelativeComplex,ChainComplex.of,ChainComplex.of_d]

end KhanSL2.Factorization
