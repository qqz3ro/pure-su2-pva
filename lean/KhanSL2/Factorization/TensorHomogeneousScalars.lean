module

public import KhanSL2.Factorization.HomogeneousCoefficientScalars
public import KhanSL2.Factorization.ShuffleComplexNaturality

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open BGG SymmetricFamily

private theorem windowScalar_inclusion {X : Type*} [AddCommGroup X] [Module ℂ X]
    {d : Module.End ℂ X} (W : BGG.Contraction.DegreeWindow d) (P : HomologyWindowSplit W)
    (hd : d.comp d=0) (f : Module.End ℂ X) (hf : f.comp d=d.comp f)
    (hc : ∀ x∈W.current, f x∈W.current) (hp : ∀ x∈W.previous, f x∈W.previous)
    (u : W.homology hd) :
    P.inclusion hd (W.homologyMap W f hd hd hf hc hp u) =
      (totalPairMap f hf).homologyMap hd hd (P.inclusion hd u) := by
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective W.boundaries u
  rfl

variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent S N]

/-- Independent coefficient scalars preserve each actual total homological degree. -/
theorem externalChainAction_mem_degree (p : ℕ) (c : R ⊗[ℂ] S)
    (z : RelativeChains M ⊗[ℂ] RelativeChains N)
    (hz : z ∈ LinearMap.range (tensorDegreeForget M N p)) :
    externalChainAction R S M N c z ∈ LinearMap.range (tensorDegreeForget M N p) := by
  induction c using TensorProduct.induction_on with
  | zero => simpa only [map_zero,LinearMap.zero_apply] using
      (LinearMap.range (tensorDegreeForget M N p)).zero_mem
  | add c d hc hd =>
    simpa only [map_add,LinearMap.add_apply] using
      (LinearMap.range (tensorDegreeForget M N p)).add_mem hc hd
  | tmul r s =>
    obtain ⟨w,rfl⟩ := hz
    refine ⟨(HomologicalComplex.tensorHom (complexMap (coefficientScalarLieHom R M r))
      (complexMap (coefficientScalarLieHom S N s))).f p w,?_⟩
    exact congrArg (fun f => f.hom w)
      (tensorDegreeForget_tensorHom (coefficientScalarLieHom R M r) (coefficientScalarLieHom S N s) p)

/-- The actual tensor homology quotient in one fixed total degree. -/
abbrev TensorHomology (p : ℕ) :=
  (tensorWindow M N p).homology (relativeTensorDifferential_comp_self M N)

/-- The given joint coefficient chain endomorphisms act on the actual degreewise cycle quotient. -/
def externalHomogeneousHomologyMap (p : ℕ) (c : R ⊗[ℂ] S) :
    Module.End ℂ (TensorHomology M N p) :=
  (tensorWindow M N p).homologyMap (tensorWindow M N p) (externalChainAction R S M N c)
    (relativeTensorDifferential_comp_self M N) (relativeTensorDifferential_comp_self M N)
    (externalChainAction_differential R S M N c)
    (externalChainAction_mem_degree R S M N p c)
    (externalChainAction_mem_degree R S M N (p+1) c)

/-- Forgetting the homogeneous degree preserves the specified scalar maps on cycle representatives. -/
theorem externalHomogeneousHomologyMap_inclusion (p : ℕ) (c : R ⊗[ℂ] S)
    (u : TensorHomology M N p) :
    (tensorHomologyWindowSplit M N p).inclusion (relativeTensorDifferential_comp_self M N)
      (externalHomogeneousHomologyMap R S M N p c u) =
    externalTensorHomologyAction R S M N c
      ((tensorHomologyWindowSplit M N p).inclusion (relativeTensorDifferential_comp_self M N) u) := by
  exact windowScalar_inclusion (tensorWindow M N p) (tensorHomologyWindowSplit M N p)
    (relativeTensorDifferential_comp_self M N) (externalChainAction R S M N c)
    (externalChainAction_differential R S M N c)
    (externalChainAction_mem_degree R S M N p c)
    (externalChainAction_mem_degree R S M N (p+1) c) u

/-- The joint action on homogeneous tensor homology is induced from the original chain action. -/
def externalHomogeneousHomologyAction (p : ℕ) : R ⊗[ℂ] S →ₐ[ℂ] Module.End ℂ (TensorHomology M N p) :=
  algebraActionOfInjective (externalTensorHomologyAction R S M N)
    ((tensorHomologyWindowSplit M N p).inclusion (relativeTensorDifferential_comp_self M N))
    ((tensorHomologyWindowSplit M N p).inclusion_injective (relativeTensorDifferential_comp_self M N))
    (externalHomogeneousHomologyMap R S M N p) (externalHomogeneousHomologyMap_inclusion R S M N p)

@[instance_reducible] def externalHomogeneousHomologyModule (p : ℕ) :
    Module (R ⊗[ℂ] S) (TensorHomology M N p) :=
  Module.compHom _ (externalHomogeneousHomologyAction R S M N p).toRingHom

attribute [local instance] externalHomogeneousHomologyModule externalTensorHomologyModule

theorem externalHomogeneousHomologyIsScalarTower (p : ℕ) :
    IsScalarTower ℂ (R ⊗[ℂ] S) (TensorHomology M N p) where
  smul_assoc c r u := LinearMap.congr_fun
    ((externalHomogeneousHomologyAction R S M N p).toLinearMap.map_smul c r) u

theorem externalHomogeneousHomologySMulCommClass (p : ℕ) :
    SMulCommClass ℂ (R ⊗[ℂ] S) (TensorHomology M N p) where
  smul_comm c r u := (map_smul (externalHomogeneousHomologyAction R S M N p r) c u).symm

/-- The genuine homogeneous inclusion respects the original independent coefficient rings. -/
def externalHomogeneousHomologyInclusion (p : ℕ) :
    TensorHomology M N p →ₗ[R ⊗[ℂ] S] TensorTotalHomology M N where
  __ := ((tensorHomologyWindowSplit M N p).inclusion
    (relativeTensorDifferential_comp_self M N)).toAddMonoidHom
  map_smul' := externalHomogeneousHomologyMap_inclusion R S M N p

end KhanSL2.Factorization
