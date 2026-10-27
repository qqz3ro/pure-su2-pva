module

public import KhanSL2.Factorization.CoefficientMapsExact
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The actual relative degree groups and differential bundled as an ordinary
nonnegative chain complex of complex vector spaces. -/

noncomputable section
open scoped TensorProduct
open CategoryTheory
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.BGGBridge

universe u

variable (N : Type u) [AddCommGroup N] [Module ℂ N]
  [LieRingModule Current N] [LieModule ℂ Current N]

/-- There is no actual CE boundary out of exterior degree zero. -/
theorem rawDifferential_eq_zero_of_degree_zero {z : RawChains N}
    (hz : z ∈ rawDegree N 0) : rawDifferential N z = 0 := by
  obtain ⟨u, rfl⟩ := hz
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul ω n =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply]
    change base (rightAction N) FreeCE.differential ((ω : PositiveCE.Cochain) ⊗ₜ[ℂ] n) = 0
    rw [base_tmul]
    have h := PositiveTransfer.sourceDifferential_eq_zero_of_degree_zero
      (Submodule.tmul_mem_baseChange_of_mem (1 : PositiveEnveloping) ω.property)
    rw [h, TensorProduct.zero_tmul, map_zero]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

theorem differential_eq_zero_of_degree_zero {z : RelativeChains N}
    (hz : z ∈ degree N 0) : differential N z = 0 := by
  obtain ⟨u, hu, rfl⟩ := hz
  change (relC N).mkQ (rawDifferential N u) = 0
  rw [rawDifferential_eq_zero_of_degree_zero N hu, map_zero]

/-- The actual boundary from degree j+1 to degree j. -/
def degreeDifferential (j : ℕ) : degree N (j + 1) →ₗ[ℂ] degree N j :=
  (differential N).restrict (fun _ h => differential_mem_degree N h)

@[simp] theorem degreeDifferential_apply (j : ℕ) (z : degree N (j + 1)) :
    (degreeDifferential N j z : RelativeChains N) = differential N z := rfl

theorem degreeDifferential_comp_succ (j : ℕ) :
    (degreeDifferential N j).comp (degreeDifferential N (j + 1)) = 0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  exact LinearMap.congr_fun (differential_comp_self N) (z : RelativeChains N)

/-- The relative CE chain complex, with its specified degree groups and boundary. -/
def complex : ChainComplex (ModuleCat ℂ) ℕ :=
  ChainComplex.of (fun j => ModuleCat.of ℂ (degree N j))
    (fun j => ModuleCat.ofHom (degreeDifferential N j))
    (fun j => ModuleCat.hom_ext (degreeDifferential_comp_succ N j))

@[simp] theorem complex_X (j : ℕ) : (complex N).X j = ModuleCat.of ℂ (degree N j) := rfl

@[simp] theorem complex_d (j : ℕ) :
    (complex N).d (j + 1) j = ModuleCat.ofHom (degreeDifferential N j) :=
  by simp only [complex, ChainComplex.of, ChainComplex.of_d]

variable {N} {M : Type u} [AddCommGroup M] [Module ℂ M]
  [LieRingModule Current M] [LieModule ℂ Current M]

/-- An actual current-module map induces an actual morphism of the bundled relative complexes. -/
def complexMap (f : N →ₗ⁅ℂ,Current⁆ M) : complex N ⟶ complex M :=
  ChainComplex.ofHom (fun j => ModuleCat.ofHom
    (coefficientDegreeMap f.toLinearMap (constantEquivariant_of_lieHom f) j)) (fun j => by
      rw [complex_d, complex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      apply Subtype.ext
      exact (coefficientMap_differential f (show RelativeChains N from (show degree N (j+1) from z).val)).symm)

end KhanSL2.Factorization
