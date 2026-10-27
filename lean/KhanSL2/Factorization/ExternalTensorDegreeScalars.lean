module

public import KhanSL2.Factorization.TensorHomogeneousScalars
public import KhanSL2.Factorization.ExternalChainScalars
public import KhanSL2.Factorization.FiniteDegreeTensor

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped TensorProduct DirectSum
open CategoryTheory
namespace KhanSL2.Factorization
open BGG SymmetricFamily

variable (R S : Type) [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
variable (M N : Type) [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module R M] [IsScalarTower ℂ R M]
  [Module ℂ N] [Module S N] [IsScalarTower ℂ S N]
  [LieRingModule Current M] [LieModule ℂ Current M] [CoefficientLinearCurrent R M]
  [LieRingModule Current N] [LieModule ℂ Current N] [CoefficientLinearCurrent S N]

/-- Restriction of the original independent coefficient action to the actual tensor degree. -/
def externalDegreeScalar (p : ℕ) (c : R ⊗[ℂ] S) :
    Module.End ℂ ((tensorComplex M N).X p) :=
  (tensorDegreeComponent M N p).comp
    ((externalChainAction R S M N c).comp (tensorDegreeForget M N p))

theorem externalDegreeScalar_forget (p : ℕ) (c : R ⊗[ℂ] S)
    (z : (tensorComplex M N).X p) :
    tensorDegreeForget M N p (externalDegreeScalar R S M N p c z) =
      externalChainAction R S M N c (tensorDegreeForget M N p z) := by
  obtain ⟨w,hw⟩ := externalChainAction_mem_degree R S M N p c
    (tensorDegreeForget M N p z) ⟨z,rfl⟩
  change tensorDegreeForget M N p (tensorDegreeComponent M N p
    (externalChainAction R S M N c (tensorDegreeForget M N p z))) = _
  rw [← hw,tensorDegreeComponent_forget]

def externalDegreeAction (p : ℕ) :
    R ⊗[ℂ] S →ₐ[ℂ] Module.End ℂ ((tensorComplex M N).X p) :=
  algebraActionOfInjective (externalChainAction R S M N) (tensorDegreeForget M N p)
    (tensorDegreeForget_injective M N p) (externalDegreeScalar R S M N p)
    (externalDegreeScalar_forget R S M N p)

@[instance_reducible] def externalDegreeModule (p : ℕ) :
    Module (R ⊗[ℂ] S) ((tensorComplex M N).X p) :=
  Module.compHom _ (externalDegreeAction R S M N p).toRingHom

attribute [local instance] externalDegreeModule

theorem externalDegreeIsScalarTower (p : ℕ) :
    IsScalarTower ℂ (R ⊗[ℂ] S) ((tensorComplex M N).X p) where
  smul_assoc c r z := LinearMap.congr_fun
    ((externalDegreeAction R S M N p).toLinearMap.map_smul c r) z

theorem externalDegreeSMulCommClass (p : ℕ) :
    SMulCommClass ℂ (R ⊗[ℂ] S) ((tensorComplex M N).X p) where
  smul_comm c r z := (map_smul (externalDegreeAction R S M N p r) c z).symm

/-- The original degree inclusion, now over the joint coefficient ring. -/
def externalDegreeForget (p : ℕ) :
    (tensorComplex M N).X p →ₗ[R ⊗[ℂ] S] (externalTotalShortComplex R S M N).X₂ where
  __ := (tensorDegreeForget M N p).toAddMonoidHom
  map_smul' := externalDegreeScalar_forget R S M N p

/-- The unchanged tensor differential is joint-coefficient-linear. -/
def externalDegreeDifferential (p : ℕ) :
    (tensorComplex M N).X (p+1) →ₗ[R ⊗[ℂ] S] (tensorComplex M N).X p where
  __ := ((tensorComplex M N).d (p+1) p).hom.toAddMonoidHom
  map_smul' c z := by
    apply tensorDegreeForget_injective M N p
    change tensorDegreeForget M N p ((tensorComplex M N).d (p+1) p
      (externalDegreeScalar R S M N (p+1) c z)) =
        tensorDegreeForget M N p (externalDegreeScalar R S M N p c
          ((tensorComplex M N).d (p+1) p z))
    rw [tensorDegreeForget_boundary,externalDegreeScalar_forget,
      externalDegreeScalar_forget,tensorDegreeForget_boundary]
    exact (LinearMap.congr_fun (externalChainAction_differential R S M N c)
      (tensorDegreeForget M N (p+1) z)).symm

/-- The original tensor complex with its actual independent coefficient action. -/
def externalTensorComplex : ChainComplex (ModuleCat (R ⊗[ℂ] S)) ℕ :=
  ChainComplex.of (fun p => ModuleCat.of (R ⊗[ℂ] S) ((tensorComplex M N).X p))
    (fun p => ModuleCat.ofHom (externalDegreeDifferential R S M N p)) (fun p => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact congrArg (fun f => f.hom z) ((tensorComplex M N).d_comp_d (p+2) (p+1) p))

@[simp] theorem externalTensorComplex_d (p : ℕ) :
    (externalTensorComplex R S M N).d (p+1) p =
      ModuleCat.ofHom (externalDegreeDifferential R S M N p) := by
  simp only [externalTensorComplex,ChainComplex.of,ChainComplex.of_d]

end KhanSL2.Factorization
