module

public import KhanSL2.Factorization.RelativeChainsDecomposition
public import KhanSL2.Factorization.RelativeChainsDualityMap

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Exterior-degree projections on actual total homology. On chains the projection
intertwines the boundary with the shifted projection, rather than commuting with it. -/

noncomputable section
open scoped DirectSum
namespace KhanSL2.Factorization
open BGG

variable (N : Type*) [AddCommGroup N] [Module ℂ N]
  [LieRingModule Current N] [LieModule ℂ Current N]

/-- Exact shifted homogeneity of the genuine relative differential. -/
theorem degreeProjection_differential (j : ℕ) (z : RelativeChains N) :
    degreeProjection N j (differential N z) =
      differential N (degreeProjection N (j+1) z) := by
  obtain ⟨u,rfl⟩ := (degreeSumEquiv N).surjective z
  induction u using DirectSum.induction_on with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | of q u =>
    rw [degreeSumEquiv_of]
    cases q with
    | zero =>
      rw [differential_eq_zero_of_degree_zero N u.property, map_zero,
        degreeProjection_of_mem_ne N (show j+1 ≠ 0 by omega) u.property, map_zero]
    | succ q =>
      have hd := differential_mem_degree N u.property
      by_cases h : j = q
      · subst j
        rw [degreeProjection_of_mem N hd, degreeProjection_of_mem N u.property]
      · rw [degreeProjection_of_mem_ne N h hd,
          degreeProjection_of_mem_ne N (show j+1 ≠ q+1 by omega) u.property, map_zero]

theorem degreeProjection_mem_ker (j : ℕ) {z : RelativeChains N}
    (hz : z ∈ LinearMap.ker (differential N)) :
    degreeProjection N j z ∈ LinearMap.ker (differential N) := by
  rw [LinearMap.mem_ker] at hz ⊢
  cases j with
  | zero => exact differential_eq_zero_of_degree_zero N (degreeProjection_mem N 0 z)
  | succ j =>
    rw [← degreeProjection_differential N j, hz, map_zero]

/-- Total homology of the actual square-zero relative differential. -/
abbrev TotalHomology := PerfectDuality.PairHomology (differential N) (differential N)
  (differential_comp_self N)

/-- Include homogeneous cycles in the total actual cycle space. -/
def homogeneousCyclesInclusion (j : ℕ) :
    (window N j).cycles →ₗ[ℂ] LinearMap.ker (differential N) where
  toFun z := ⟨z.val,z.property.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Project a total cycle to its actual exterior-degree component. -/
def homogeneousCyclesProjection (j : ℕ) :
    LinearMap.ker (differential N) →ₗ[ℂ] (window N j).cycles :=
  ((degreeProjection N j).comp (LinearMap.ker (differential N)).subtype).codRestrict _
    (fun z => ⟨degreeProjection_mem N j z.val, degreeProjection_mem_ker N j z.property⟩)

/-- Degree-j homology includes canonically into the total quotient. -/
def homogeneousHomologyInclusion (j : ℕ) : Homology N j →ₗ[ℂ] TotalHomology N :=
  (window N j).boundaries.mapQ
    (PerfectDuality.pairBoundaries (differential N) (differential N))
    (homogeneousCyclesInclusion N j) (by
      rintro z ⟨u,hu,huz⟩
      exact ⟨u,huz⟩)

/-- Exact homogeneity makes the degree projection well-defined on boundaries. -/
def homogeneousHomologyProjection (j : ℕ) : TotalHomology N →ₗ[ℂ] Homology N j :=
  (PerfectDuality.pairBoundaries (differential N) (differential N)).mapQ
    (window N j).boundaries (homogeneousCyclesProjection N j) (by
      rintro z ⟨u,huz⟩
      refine ⟨degreeProjection N (j+1) u,degreeProjection_mem N (j+1) u,?_⟩
      change differential N (degreeProjection N (j+1) u) = degreeProjection N j z.val
      rw [← degreeProjection_differential N j, huz]
      rfl)

@[simp] theorem homogeneousHomologyProjection_inclusion (j : ℕ) (z : Homology N j) :
    homogeneousHomologyProjection N j (homogeneousHomologyInclusion N j z) = z := by
  obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective (window N j).boundaries z
  change Submodule.Quotient.mk
    (homogeneousCyclesProjection N j (homogeneousCyclesInclusion N j u)) =
      Submodule.Quotient.mk u
  congr 1
  apply Subtype.ext
  exact degreeProjection_of_mem N u.property.1

theorem homogeneousHomologyInclusion_injective (j : ℕ) :
    Function.Injective (homogeneousHomologyInclusion N j) :=
  Function.LeftInverse.injective (homogeneousHomologyProjection_inclusion N j)

/-- A bijective map respecting specified split homogeneous components restricts
bijectively to each component. This is the degreewise step after total duality. -/
theorem bijective_of_split_components
    {A B A' B' : Type*}
    (iA : A → A') (pA : A' → A) (iB : B → B') (pB : B' → B)
    (hA : Function.LeftInverse pA iA) (hB : Function.LeftInverse pB iB)
    (f : A → B) (F : A' → B') (hF : Function.Bijective F)
    (hi : ∀ a, iB (f a) = F (iA a))
    (hp : ∀ a, f (pA a) = pB (F a)) : Function.Bijective f := by
  constructor
  · intro a b hab
    apply hA.injective
    apply hF.injective
    rw [← hi, ← hi, hab]
  · intro b
    obtain ⟨a,ha⟩ := hF.surjective (iB b)
    exact ⟨pA a, by rw [hp,ha,hB b]⟩

end KhanSL2.Factorization
