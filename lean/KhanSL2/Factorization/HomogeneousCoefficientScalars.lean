module

public import KhanSL2.Factorization.ExternalKunneth

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct
namespace KhanSL2.Factorization
open BGG SymmetricFamily

/-- Verify the algebra laws of specified endomorphisms using a faithful invariant inclusion.
The endomorphisms themselves are supplied, rather than defined by transport. -/
def algebraActionOfInjective {R X Y : Type*} [CommRing R] [Algebra ℂ R]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : R →ₐ[ℂ] Module.End ℂ X) (ι : Y →ₗ[ℂ] X) (hι : Function.Injective ι)
    (f : R → Module.End ℂ Y) (hf : ∀ r y, ι (f r y)=ρ r (ι y)) :
    R →ₐ[ℂ] Module.End ℂ Y where
  toFun := f
  map_zero' := by
    ext y
    apply hι
    rw [hf]
    simp
  map_one' := by
    ext y
    apply hι
    rw [hf]
    simp
  map_add' r s := by
    ext y
    apply hι
    rw [hf]
    change _ = ι (f r y+f s y)
    rw [ι.map_add,hf,hf]
    exact LinearMap.congr_fun (map_add ρ r s) (ι y)
  map_mul' r s := by
    ext y
    apply hι
    rw [hf]
    change _ = ι (f r (f s y))
    rw [hf,hf]
    exact LinearMap.congr_fun (map_mul ρ r s) (ι y)
  commutes' c := by
    ext y
    apply hι
    rw [hf,ρ.commutes]
    change c • ι y = ι (c • y)
    exact (ι.map_smul c y).symm

section Naturality
variable {M N : Type} [AddCommGroup M] [AddCommGroup N]
  [Module ℂ M] [Module ℂ N]
  [LieRingModule Current M] [LieModule ℂ Current M]
  [LieRingModule Current N] [LieModule ℂ Current N]

/-- Inclusion of homogeneous classes preserves the original coefficient homology maps. -/
theorem homogeneousHomologyInclusion_homologyMap (f : M →ₗ⁅ℂ,Current⁆ N) (p : ℕ)
    (u : Homology M p) :
    homogeneousHomologyInclusion N p (homologyMap f p u) =
      coefficientTotalHomologyMap f (homogeneousHomologyInclusion M p u) := by
  obtain ⟨z,rfl⟩ := Submodule.mkQ_surjective (window M p).boundaries u
  rfl

end Naturality

variable (R : Type) [CommRing R] [Algebra ℂ R]
variable (M : Type) [AddCommGroup M] [Module ℂ M]
  [LieRingModule Current M] [LieModule ℂ Current M] [Module R M] [IsScalarTower ℂ R M] [CoefficientLinearCurrent R M]

/-- The original coefficient endomorphisms induce the prescribed degreewise action on cycle classes. -/
def coefficientHomogeneousHomologyAction (p : ℕ) : R →ₐ[ℂ] Module.End ℂ (Homology M p) :=
  algebraActionOfInjective (coefficientTotalHomologyAction R M)
    (homogeneousHomologyInclusion M p) (homogeneousHomologyInclusion_injective M p)
    (fun r => homologyMap (coefficientScalarLieHom R M r) p)
    (fun r u => homogeneousHomologyInclusion_homologyMap (coefficientScalarLieHom R M r) p u)

@[instance_reducible] def coefficientHomogeneousHomologyModule (p : ℕ) : Module R (Homology M p) :=
  Module.compHom _ (coefficientHomogeneousHomologyAction R M p).toRingHom

attribute [local instance] coefficientHomogeneousHomologyModule coefficientTotalHomologyModule

@[simp] theorem coefficientHomogeneousHomology_smul (p : ℕ) (r : R) (u : Homology M p) :
    r • u = homologyMap (coefficientScalarLieHom R M r) p u := rfl

theorem coefficientHomogeneousHomologyIsScalarTower (p : ℕ) : IsScalarTower ℂ R (Homology M p) where
  smul_assoc c r u := LinearMap.congr_fun
    ((coefficientHomogeneousHomologyAction R M p).toLinearMap.map_smul c r) u

theorem coefficientHomogeneousHomologySMulCommClass (p : ℕ) : SMulCommClass ℂ R (Homology M p) where
  smul_comm c r u := (map_smul (coefficientHomogeneousHomologyAction R M p r) c u).symm

/-- The actual degree inclusion is coefficient-linear for the original induced actions. -/
def coefficientHomogeneousHomologyInclusion (p : ℕ) : Homology M p →ₗ[R] TotalHomology M where
  __ := (homogeneousHomologyInclusion M p).toAddMonoidHom
  map_smul' r u := homogeneousHomologyInclusion_homologyMap (coefficientScalarLieHom R M r) p u

end KhanSL2.Factorization
