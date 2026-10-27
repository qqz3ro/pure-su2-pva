module

public import KhanSL2.BGGBridge.Transfer
public import KhanSL2.BGG.FreeCESupport
public import KhanSL2.BGG.RelativeCochainsDegree
public import KhanSL2.BGG.ContractionDegreeHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Actual relative CE chains with arbitrary current-algebra coefficients.
The chains are the existing positive exterior model tensored with the coefficients,
modulo the diagonal constant sl2 action. No semisimplicity is assumed here. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.BGGBridge

variable (N : Type*) [AddCommGroup N] [Module ℂ N]
  [LieRingModule Current N] [LieModule ℂ Current N]

/-- The concrete positive CE chain space before constant coinvariants. -/
abbrev RawChains := ChainN N

/-- Relative chains are the actual quotient by the diagonal constant Lie action. -/
abbrev RelativeChains := RawChains N ⧸ relC N

/-- The differential is the existing coefficient base change of the free CE differential. -/
abbrev rawDifferential : Module.End ℂ (RawChains N) := dC N

/-- The differential on the actual constant-coinvariant quotient. -/
abbrev differential : Module.End ℂ (RelativeChains N) := dCq N

@[simp] theorem differential_mk (z : RawChains N) :
    differential N (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (rawDifferential N z) := rfl

/-- The explicit finite CE boundary, including the coefficient action. -/
theorem rawDifferential_tmul (S : Finset PositiveCE.Mode) (ω : PositiveCE.Cochain)
    (hω : FiniteExterior.supportModes ω ⊆ S) (n : N) :
    rawDifferential N (ω ⊗ₜ[ℂ] n) = PositiveCE.boundary ω ⊗ₜ[ℂ] n -
      ∑ k ∈ S, PositiveCE.contract k ω ⊗ₜ[ℂ]
        ⁅(FreeCE.lieGenerator k : Current), n⁆ := by
  rw [rawDifferential, dC, base_tmul,
    FreeCE.differential_tmul_finite S 1 ω hω, TensorProduct.add_tmul,
    map_add, TensorProduct.sum_tmul, map_sum, ev_tmul_tmul, ract_one,
    Module.End.one_apply]
  simp only [ev_tmul_tmul, one_mul, FreeCE.ueGenerator, ract_ι,
    TensorProduct.tmul_neg, Finset.sum_neg_distrib]
  abel

@[simp] theorem rawDifferential_one_tmul (n : N) :
    rawDifferential N ((1 : PositiveCE.Cochain) ⊗ₜ[ℂ] n) = 0 := by
  rw [rawDifferential, dC, base_tmul, FreeCE.differential_tmul_one,
    TensorProduct.zero_tmul, map_zero]

/-- Square-zero follows from the genuine free CE differential by coefficient base change. -/
theorem rawDifferential_comp_self :
    (rawDifferential N).comp (rawDifferential N) = 0 := by
  change (dC N).comp (dC N) = 0
  rw [dC, ← base_comp]
  have h : FreeCE.differential.comp FreeCE.differential = 0 :=
    LinearMap.ext fun u => FreeCE.differential_square_zero u
  rw [h, base_zero]

theorem differential_comp_self : (differential N).comp (differential N) = 0 := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro z
  have h := LinearMap.congr_fun (rawDifferential_comp_self N) z
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  change Submodule.Quotient.mk (rawDifferential N (rawDifferential N z)) =
    (0 : RelativeChains N)
  rw [h, Submodule.Quotient.mk_zero]

/-- Exterior degree j before coinvariants; no coefficient grading is imposed. -/
def rawDegree (j : ℕ) : Submodule ℂ (RawChains N) := tensorLeft (degC j)

/-- Exterior degree j in the relative coinvariant quotient. -/
def degree (j : ℕ) : Submodule ℂ (RelativeChains N) :=
  (rawDegree N j).map (relC N).mkQ

/-- The actual coefficient boundary lowers exterior degree. -/
theorem rawDifferential_mem_degree {j : ℕ} {z : RawChains N}
    (hz : z ∈ rawDegree N (j + 1)) : rawDifferential N z ∈ rawDegree N j :=
  base_mem_tensorLeft (rightAction N) _ (fun _ ha =>
    PositiveTransfer.sourceDifferential_mem_degree
      (Submodule.tmul_mem_baseChange_of_mem 1 ha)) hz

theorem differential_mem_degree {j : ℕ} {z : RelativeChains N}
    (hz : z ∈ degree N (j + 1)) : differential N z ∈ degree N j := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact ⟨rawDifferential N w, rawDifferential_mem_degree N hw, rfl⟩

/-- The actual degree-j relative chain window and its incoming differential. -/
def window (j : ℕ) : Contraction.DegreeWindow (differential N) where
  current := degree N j
  previous := degree N (j + 1)
  differential_mem := fun _ h => differential_mem_degree N h

/-- Relative CE homology, defined as cycles modulo boundaries in degree j. -/
abbrev Homology (j : ℕ) := (window N j).homology (differential_comp_self N)

end KhanSL2.Factorization

