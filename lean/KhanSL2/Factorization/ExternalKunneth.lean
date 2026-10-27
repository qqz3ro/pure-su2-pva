module

public import KhanSL2.Factorization.ExternalTensor
public import KhanSL2.Factorization.HomologyScalarAction
public import KhanSL2.Factorization.CoefficientChainScalars

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

/-! Field Künneth with both original independent coefficient actions retained.
The action on tensor homology is induced from actual scalar maps on chains,
not transported along the Künneth equivalence. -/
noncomputable section
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily
variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent S N]

/-- Joint original scalar action on the signed total tensor of relative CE chains. -/
def externalChainAction : R ⊗[ℂ] S →ₐ[ℂ] Module.End ℂ (RelativeChains M ⊗[ℂ] RelativeChains N) :=
  (Module.endTensorEndAlgHom (R:=ℂ) (S:=ℂ) (A:=ℂ)
    (M:=RelativeChains M) (N:=RelativeChains N)).comp
      (Algebra.TensorProduct.map (coefficientChainAction R M) (coefficientChainAction S N))

/-- The joint action commutes with the original signed tensor differential. -/
theorem externalChainAction_differential (c : R ⊗[ℂ] S) :
    (externalChainAction R S M N c).comp (relativeTensorDifferential M N) =
      (relativeTensorDifferential M N).comp (externalChainAction R S M N c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c d hc hd => simp only [map_add,LinearMap.add_comp,LinearMap.comp_add,hc,hd]
  | tmul r s =>
    apply LinearMap.ext
    exact tensorCoefficientMap_differential (coefficientScalarLieHom R M r) (coefficientScalarLieHom S N s)

/-- The induced joint action on genuine tensor cycle classes. -/
def externalTensorHomologyAction : R ⊗[ℂ] S →ₐ[ℂ] Module.End ℂ (TensorTotalHomology M N) :=
  homologyScalarAction (R ⊗[ℂ] S) (relativeTensorDifferential M N)
    (relativeTensorDifferential_comp_self M N) (externalChainAction R S M N)
    (externalChainAction_differential R S M N)

@[instance_reducible] def externalTensorHomologyModule : Module (R ⊗[ℂ] S) (TensorTotalHomology M N) :=
  Module.compHom _ (externalTensorHomologyAction R S M N).toRingHom

attribute [local instance] externalTensorHomologyModule

/-- Pure joint scalars act by the unchanged tensor coefficient homology maps. -/
theorem externalTensorHomology_smul_tmul (r : R) (s : S) (z : TensorTotalHomology M N) :
    (r ⊗ₜ[ℂ] s) • z = tensorCoefficientTotalHomologyMap
      (coefficientScalarLieHom R M r) (coefficientScalarLieHom S N s) z := rfl

/-- The genuine complex scalar tower for tensor homology. -/
theorem externalTensorHomologyIsScalarTower : IsScalarTower ℂ (R ⊗[ℂ] S) (TensorTotalHomology M N) where
  smul_assoc c r z := LinearMap.congr_fun
    ((externalTensorHomologyAction R S M N).toLinearMap.map_smul c r) z

theorem externalTensorHomologySMulCommClass : SMulCommClass ℂ (R ⊗[ℂ] S) (TensorTotalHomology M N) where
  smul_comm c r z := (map_smul (externalTensorHomologyAction R S M N r) c z).symm

attribute [local instance] coefficientTotalHomologyModule coefficientTotalHomologyIsScalarTower
  coefficientTotalHomologySMulCommClass

/-- The field Künneth equivalence is linear for the two independent original coefficient rings. -/
def externalKunnethEquiv :
    ExternalTensor R S (TotalHomology M) (TotalHomology N) ≃ₗ[R ⊗[ℂ] S] TensorTotalHomology M N where
  toFun z := totalKunnethEquiv M N z
  invFun z := (totalKunnethEquiv M N).symm z
  left_inv z := (totalKunnethEquiv M N).symm_apply_apply z
  right_inv z := (totalKunnethEquiv M N).apply_symm_apply z
  map_add' := map_add _
  map_smul' c z := by
    induction c using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => simp only [add_smul,map_add,hc,hd]
    | tmul r s =>
      change totalKunnethEquiv M N
        (TensorProduct.map (coefficientTotalHomologyMap (coefficientScalarLieHom R M r))
          (coefficientTotalHomologyMap (coefficientScalarLieHom S N s)) z) =
        tensorCoefficientTotalHomologyMap (coefficientScalarLieHom R M r)
          (coefficientScalarLieHom S N s) (totalKunnethEquiv M N z)
      exact (totalKunnethEquiv_natural (coefficientScalarLieHom R M r)
        (coefficientScalarLieHom S N s) z).symm

end KhanSL2.Factorization
