module

public import KhanSL2.BGG.RelativeCochainsDegree
public import KhanSL2.BGG.ContractionDegreeHomology

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace KhanSL2.BGG.RelativeCochains
open scoped RelativeCochains

variable (M : Type*) [AddCommGroup M] [Module ℂ M]
  [Module Enveloping M] [IsScalarTower ℂ Enveloping M]

/-- The actual full relative CE cochain differential is square-zero as a linear map. -/
theorem differential_comp_self_zero : (differential M).comp (differential M) = 0 := by
  apply LinearMap.ext
  intro f
  exact differential_square_zero M f

/-- The actual harmonic coefficient differential is square-zero as a linear map. -/
theorem harmonicDifferential_comp_self_zero :
    (harmonicDifferential M).comp (harmonicDifferential M) = 0 := by
  apply LinearMap.ext
  intro f
  exact harmonicDifferential_square_zero M f

/-- The actual CE cochains and preceding cochains in a fixed cohomological degree. -/
def freeWindow (p : ℕ) : Contraction.DegreeWindow (differential M) where
  current := freeDegree M p
  previous := match p with | 0 => ⊥ | q+1 => freeDegree M q
  differential_mem := by
    intro f hf
    cases p with
    | zero =>
      have hf0 : f = 0 := hf
      rw [hf0, map_zero]
      exact (freeDegree M 0).zero_mem
    | succ p => exact differential_mem_freeDegree M hf

/-- The corresponding two degrees in the actual BGG harmonic Hom complex. -/
def harmonicWindow (p : ℕ) : Contraction.DegreeWindow (harmonicDifferential M) where
  current := harmonicDegree M p
  previous := match p with | 0 => ⊥ | q+1 => harmonicDegree M q
  differential_mem := by
    intro f hf
    cases p with
    | zero =>
      have hf0 : f = 0 := hf
      rw [hf0, map_zero]
      exact (harmonicDegree M 0).zero_mem
    | succ p => exact harmonicDifferential_mem_harmonicDegree M hf

/-- Ordinary algebraic relative CE cohomology: actual degree-p full-Hom cycles
modulo differentials of degree-(p-1) cochains. No energy-support restriction is imposed. -/
abbrev Cohomology (p : ℕ) := (freeWindow M p).homology (differential_comp_self_zero M)

/-- Cohomology of the constructed BGG Hom complex in the same cohomological degree. -/
abbrev BGGCohomology (p : ℕ) :=
  (harmonicWindow M p).homology (harmonicDifferential_comp_self_zero M)

set_option maxHeartbeats 800000 in
/-- The actual HPL comparison induces an isomorphism on ordinary algebraic
relative cohomology in every degree, for every compatible current-algebra module. -/
def cohomologyEquiv (p : ℕ) : Cohomology M p ≃ₗ[ℂ] BGGCohomology M p := by
  apply Contraction.degreeHomologyEquiv (comparison M) (differential_comp_self_zero M)
    (freeWindow M p) (harmonicWindow M p)
  · intro f hf
    exact fromHarmonic_mem_degree M hf
  · intro f hf
    exact toHarmonic_mem_degree M hf
  · intro f hf
    cases p with
    | zero =>
      have hf0 : f = 0 := hf
      rw [hf0, map_zero]
      exact Submodule.zero_mem _
    | succ p => exact fromHarmonic_mem_degree M hf
  · intro f hf
    cases p with
    | zero =>
      have hf0 : f = 0 := hf
      rw [hf0, map_zero]
      exact Submodule.zero_mem _
    | succ p => exact toHarmonic_mem_degree M hf
  · intro f hf
    cases p with
    | zero =>
      change comparisonHomotopy M f ∈ (⊥ : Submodule ℂ (FreeHom M))
      exact comparisonHomotopy_eq_zero_of_degree_zero M hf
    | succ p => exact comparisonHomotopy_mem_degree M hf

/-- The specified BGG Hom complex computes ordinary algebraic relative cohomology. -/
theorem relative_cohomology_computed_by_bgg (p : ℕ) :
    Nonempty (Cohomology M p ≃ₗ[ℂ] BGGCohomology M p) := ⟨cohomologyEquiv M p⟩

end KhanSL2.BGG.RelativeCochains