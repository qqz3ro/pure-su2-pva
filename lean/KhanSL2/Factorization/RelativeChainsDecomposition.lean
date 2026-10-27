module

public import KhanSL2.Factorization.RelativeChainsGrading

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Actual relative chains are the internal direct sum of their exterior-degree groups. -/

noncomputable section
open scoped TensorProduct DirectSum
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.BGGBridge

variable (N : Type*) [AddCommGroup N] [Module ℂ N]
  [LieRingModule Current N] [LieModule ℂ Current N]

/-- Projection recovers each component of the canonical sum of homogeneous chains. -/
theorem degreeProjection_directSum (v : ⨁ j, degree N j) (j : ℕ) :
    degreeProjection N j (DirectSum.coeLinearMap (degree N) v) = (v j).val := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of q v =>
    rw [DirectSum.coeLinearMap_of]
    by_cases h : q = j
    · subst q
      rw [degreeProjection_of_mem N v.property]
      simp
    · rw [degreeProjection_of_mem_ne N (Ne.symm h) v.property]
      simp [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
  | add u v hu hv =>
    simp only [map_add, hu, hv]
    rfl

/-- The quotient has no components outside the usual finite exterior degrees. -/
theorem degree_iSup_eq_top : (⨆ j, degree N j) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective (relC N) z
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul ω n =>
    induction ω using Finsupp.induction_linear with
    | zero => simp
    | single s c =>
      apply Submodule.mem_iSup_of_mem s.card
      refine ⟨Finsupp.single s c ⊗ₜ[ℂ] n, ?_, rfl⟩
      exact ⟨(⟨Finsupp.single s c, Finsupp.single_mem_supported ℂ c rfl⟩ :
        degC s.card) ⊗ₜ[ℂ] n, rfl⟩
    | add u v hu hv =>
      simpa only [TensorProduct.add_tmul, map_add] using Submodule.add_mem _ hu hv
  | add u v hu hv => simpa only [map_add] using Submodule.add_mem _ hu hv

/-- Exterior degree is a genuine internal direct-sum decomposition after coinvariants. -/
theorem degree_isInternal : DirectSum.IsInternal (degree N) := by
  change Function.Bijective (DirectSum.coeLinearMap (degree N))
  constructor
  · intro v w h
    apply DFinsupp.ext
    intro j
    apply Subtype.ext
    rw [← degreeProjection_directSum N v j, ← degreeProjection_directSum N w j, h]
  · apply LinearMap.range_eq_top.mp
    rw [DirectSum.range_coeLinearMap, degree_iSup_eq_top N]

/-- The canonical finite homogeneous expansion of an actual relative chain. -/
def degreeSumEquiv : (⨁ j, degree N j) ≃ₗ[ℂ] RelativeChains N :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (degree N)) (degree_isInternal N)

@[simp] theorem degreeSumEquiv_apply (v : ⨁ j, degree N j) :
    degreeSumEquiv N v = DirectSum.coeLinearMap (degree N) v := rfl

@[simp] theorem degreeSumEquiv_of (j : ℕ) (z : degree N j) :
    degreeSumEquiv N (DirectSum.of (fun j => degree N j) j z) = z.val :=
  DirectSum.coeLinearMap_of _ j z

/-- Homogeneous components of the finite expansion are the specified quotient projections. -/
theorem degreeSumEquiv_symm_apply (z : RelativeChains N) (j : ℕ) :
    (degreeSumEquiv N).symm z j = degreeComponent N j z := by
  apply Subtype.ext
  change ((degreeSumEquiv N).symm z j).val = degreeProjection N j z
  have h := degreeProjection_directSum N ((degreeSumEquiv N).symm z) j
  rw [← degreeSumEquiv_apply, LinearEquiv.apply_symm_apply] at h
  exact h.symm

end KhanSL2.Factorization
