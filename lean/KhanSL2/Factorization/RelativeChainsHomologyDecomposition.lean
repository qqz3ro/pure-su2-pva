module

public import KhanSL2.Factorization.RelativeChainsHomologyWindow
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! A finite homogeneous decomposition of chains induces the canonical direct-sum
homology decomposition. The projections need only satisfy the actual shifted
boundary identity, not commute with the differential. -/
noncomputable section
open scoped DirectSum BigOperators
namespace KhanSL2.Factorization
open BGG.Contraction

namespace HomologyWindowSplit
variable {A : Type*} [AddCommGroup A] [Module ℂ A]
  {d : Module.End ℂ A} {ι : Type*} [DecidableEq ι]
  (W : ι → DegreeWindow d) (P : ∀ i, HomologyWindowSplit (W i))
  (hd : d.comp d = 0)

def sumInclusion : (⨁ i, (W i).homology hd) →ₗ[ℂ]
    PerfectDuality.PairHomology d d hd :=
  DirectSum.toModule ℂ ι _ (fun i => (P i).inclusion hd)

@[simp] theorem sumInclusion_of (i : ι) (u : (W i).homology hd) :
    sumInclusion W P hd (DirectSum.of (fun i => (W i).homology hd) i u) =
      (P i).inclusion hd u :=
  DirectSum.toModule_lof ℂ (φ := fun i => (P i).inclusion hd) i u

omit [DecidableEq ι] in
theorem projection_inclusion_ne
    (hc : ∀ i j, i ≠ j → ∀ u ∈ (W j).current, (P i).projection u = 0)
    {i j : ι} (hij : i ≠ j) (u : (W j).homology hd) :
    (P i).homologyProjection hd ((P j).inclusion hd u) = 0 := by
  obtain ⟨v,rfl⟩ := Submodule.mkQ_surjective (W j).boundaries u
  change Submodule.Quotient.mk ((P i).cycleProjection ((P j).cycleInclusion v)) = 0
  have hz : (P i).cycleProjection ((P j).cycleInclusion v) = 0 := by
    apply Subtype.ext
    exact hc i j hij v.val v.property.1
  rw [hz,Submodule.Quotient.mk_zero]

theorem projection_sumInclusion
    (hc : ∀ i j, i ≠ j → ∀ u ∈ (W j).current, (P i).projection u = 0)
    (u : ⨁ i, (W i).homology hd) (i : ι) :
    (P i).homologyProjection hd (sumInclusion W P hd u) = u i := by
  induction u using DirectSum.induction_on with
  | zero => simp
  | of j u =>
    rw [sumInclusion_of]
    by_cases hij : i = j
    · subst j
      rw [projection_inclusion]
      simp
    · rw [projection_inclusion_ne W P hd hc hij]
      exact (DirectSum.of_eq_of_ne (β := fun i => (W i).homology hd) j i u hij).symm
  | add u v hu hv =>
    simp only [map_add,hu,hv]
    rfl

theorem sumInclusion_injective
    (hc : ∀ i j, i ≠ j → ∀ u ∈ (W j).current, (P i).projection u = 0) :
    Function.Injective (sumInclusion W P hd) := by
  intro u v huv
  apply DFinsupp.ext
  intro i
  rw [← projection_sumInclusion W P hd hc u i,
    ← projection_sumInclusion W P hd hc v i,huv]

theorem sumInclusion_surjective
    (hf : ∀ u : A, ∃ s : Finset ι, ∑ i ∈ s, (P i).projection u = u) :
    Function.Surjective (sumInclusion W P hd) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨u,rfl⟩ := Submodule.mkQ_surjective (PerfectDuality.pairBoundaries d d) z
  obtain ⟨s,hs⟩ := hf u.val
  have hsum : ∑ i ∈ s, (P i).cycleInclusion ((P i).cycleProjection u) = u := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hs
  rw [← hsum,map_sum]
  apply Submodule.sum_mem
  intro i hi
  refine ⟨DirectSum.of (fun i => (W i).homology hd) i
    (Submodule.Quotient.mk ((P i).cycleProjection u)),?_⟩
  rw [sumInclusion_of]
  rfl

/-- Canonical sum of the specified homogeneous homology inclusions. -/
def decompositionEquiv
    (hc : ∀ i j, i ≠ j → ∀ u ∈ (W j).current, (P i).projection u = 0)
    (hf : ∀ u : A, ∃ s : Finset ι, ∑ i ∈ s, (P i).projection u = u) :
    (⨁ i, (W i).homology hd) ≃ₗ[ℂ] PerfectDuality.PairHomology d d hd :=
  LinearEquiv.ofBijective (sumInclusion W P hd)
    ⟨sumInclusion_injective W P hd hc,sumInclusion_surjective W P hd hf⟩

end HomologyWindowSplit

/-- A finite-support graded model supplies a finite projection reconstruction.
Several grading labels may contribute to the same total degree. -/
theorem finite_projection_sum_of_directSum
    {A : Type*} [AddCommGroup A] [Module ℂ A]
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (B : κ → Type*) [∀ k, AddCommGroup (B k)] [∀ k, Module ℂ (B k)]
    (e : (⨁ k, B k) ≃ₗ[ℂ] A) (f : κ → ι) (P : ι → Module.End ℂ A)
    (he : ∀ i k v, P i (e (DirectSum.of B k v)) =
      if i = f k then e (DirectSum.of B k v) else 0) (u : A) :
    ∃ s : Finset ι, ∑ i ∈ s, P i u = u := by
  classical
  let v := e.symm u
  refine ⟨v.support.image f,?_⟩
  have hv : u = ∑ k ∈ v.support, e (DirectSum.of B k (v k)) := by
    rw [← map_sum,DirectSum.sum_support_of]
    exact (e.apply_symm_apply u).symm
  conv_lhs => rw [hv]
  simp only [map_sum]
  rw [Finset.sum_comm]
  calc
    (∑ k ∈ v.support, ∑ i ∈ v.support.image f, P i (e (DirectSum.of B k (v k)))) =
        ∑ k ∈ v.support, e (DirectSum.of B k (v k)) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [he]
      simp [Finset.mem_image_of_mem f hk]
    _ = u := hv.symm

variable (N : Type*) [AddCommGroup N] [Module ℂ N]
  [LieRingModule BGG.Current N] [LieModule ℂ BGG.Current N]

theorem degreeProjection_finite_sum (u : RelativeChains N) :
    ∃ s : Finset ℕ, ∑ j ∈ s, degreeProjection N j u = u := by
  apply finite_projection_sum_of_directSum (fun j => degree N j) (degreeSumEquiv N) id
    (degreeProjection N)
  intro i j v
  rw [degreeSumEquiv_of]
  change degreeProjection N i v.val = if i = j then v.val else 0
  by_cases h : i = j
  · subst j
    rw [if_pos rfl,degreeProjection_of_mem N v.property]
  · rw [if_neg h,degreeProjection_of_mem_ne N h v.property]

/-- The actual total homology is the algebraic sum of its exterior degrees. -/
def homologySumEquiv : (⨁ j, Homology N j) ≃ₗ[ℂ] TotalHomology N :=
  HomologyWindowSplit.decompositionEquiv (window N) (relativeHomologyWindowSplit N)
    (differential_comp_self N)
    (fun _i _j hij _u hu => degreeProjection_of_mem_ne N hij hu)
    (degreeProjection_finite_sum N)

@[simp] theorem homologySumEquiv_of (j : ℕ) (u : Homology N j) :
    homologySumEquiv N (DirectSum.of (Homology N) j u) =
      homogeneousHomologyInclusion N j u := by
  change HomologyWindowSplit.sumInclusion (window N) (relativeHomologyWindowSplit N)
    (differential_comp_self N) (DirectSum.of (Homology N) j u) = _
  rw [HomologyWindowSplit.sumInclusion_of]
  rfl

end KhanSL2.Factorization
