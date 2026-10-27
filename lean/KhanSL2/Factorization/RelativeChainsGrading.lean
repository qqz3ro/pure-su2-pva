module

public import KhanSL2.Factorization.RelativeChainsComplex
public import KhanSL2.BGG.ColorRootGrading

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Actual exterior-degree projections descend through the constant-sl2 relations. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Factorization
open KhanSL2.BGG KhanSL2.BGGBridge

/-- Project positive exterior coordinates to exterior degree j. -/
abbrev exteriorDegreeProjection (j : ℕ) : Module.End ℂ PositiveCE.Cochain :=
  BasisGrading.projection Finset.card j

theorem positiveAction_mem_degC (x : G) {j : ℕ} {u : PositiveCE.Cochain}
    (hu : u ∈ degC j) : ColorRoot.positiveAction x u ∈ degC j := by
  rw [← Finsupp.sum_single u]
  change ColorRoot.positiveAction x (∑ s ∈ u.support, Finsupp.single s (u s)) ∈ degC j
  rw [map_sum]
  apply Submodule.sum_mem
  intro s hs
  have h := PositiveCE.positiveAction_mem_piece x
    (Finsupp.single_mem_supported ℂ (u s)
      (show s.card = s.card ∧ PositiveCE.monomialEnergy s = PositiveCE.monomialEnergy s from
        ⟨rfl, rfl⟩))
  intro t ht
  exact (h ht).1.trans (hu hs)

theorem exteriorDegreeProjection_action (j : ℕ) (x : G) (u : PositiveCE.Cochain) :
    exteriorDegreeProjection j (ColorRoot.positiveAction x u) =
      ColorRoot.positiveAction x (exteriorDegreeProjection j u) :=
  BasisGrading.projection_linearMap Finset.card (ColorRoot.positiveAction x) id
    Function.injective_id (fun _ _ h => positiveAction_mem_degC x h) j u

variable (N : Type*) [AddCommGroup N] [Module ℂ N]

/-- Exterior-degree projection before constant coinvariants. -/
def rawDegreeProjection (j : ℕ) : Module.End ℂ (RawChains N) :=
  LinearMap.rTensor N (exteriorDegreeProjection j)

@[simp] theorem rawDegreeProjection_tmul (j : ℕ) (u : PositiveCE.Cochain) (n : N) :
    rawDegreeProjection N j (u ⊗ₜ[ℂ] n) = exteriorDegreeProjection j u ⊗ₜ[ℂ] n := rfl

theorem rawDegreeProjection_mem (j : ℕ) (z : RawChains N) :
    rawDegreeProjection N j z ∈ rawDegree N j := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u n =>
    exact ⟨(⟨exteriorDegreeProjection j u, BasisGrading.projection_mem Finset.card j u⟩ :
      degC j) ⊗ₜ[ℂ] n, rfl⟩
  | add z w hz hw => simpa only [map_add] using Submodule.add_mem _ hz hw

theorem rawDegreeProjection_of_mem {j : ℕ} {z : RawChains N} (hz : z ∈ rawDegree N j) :
    rawDegreeProjection N j z = z := by
  obtain ⟨u, rfl⟩ := hz
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul u n =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, rawDegreeProjection_tmul,
      BasisGrading.projection_of_mem Finset.card u.property]
  | add u v hu hv => simp only [map_add, hu, hv]

theorem rawDegreeProjection_of_mem_ne {j q : ℕ} (hjq : j ≠ q) {z : RawChains N}
    (hz : z ∈ rawDegree N q) : rawDegreeProjection N j z = 0 := by
  obtain ⟨u, rfl⟩ := hz
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul u n =>
    rw [LinearMap.rTensor_tmul, Submodule.subtype_apply, rawDegreeProjection_tmul,
      BasisGrading.projection_of_mem_ne Finset.card hjq u.property, TensorProduct.zero_tmul]
  | add u v hu hv => simp only [map_add, hu, hv, add_zero]

variable [LieRingModule Current N] [LieModule ℂ Current N]

theorem rawDegreeProjection_actC (j : ℕ) (x : G) (z : RawChains N) :
    rawDegreeProjection N j (actC N x z) = actC N x (rawDegreeProjection N j z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul u n =>
    simp only [actC, diag_tmul, map_add, rawDegreeProjection_tmul,
      exteriorDegreeProjection_action]
  | add z w hz hw => simp only [map_add, hz, hw]

/-- The actual degree projection on the relative coinvariant quotient. -/
def degreeProjection (j : ℕ) : Module.End ℂ (RelativeChains N) :=
  (relC N).mapQ (relC N) (rawDegreeProjection N j)
    (le_comap_of_commute (actC N) (actC N) (rawDegreeProjection N j)
      (rawDegreeProjection_actC N j))

@[simp] theorem degreeProjection_mk (j : ℕ) (z : RawChains N) :
    degreeProjection N j ((relC N).mkQ z) =
      (relC N).mkQ (rawDegreeProjection N j z) := rfl

theorem degreeProjection_mem (j : ℕ) (z : RelativeChains N) :
    degreeProjection N j z ∈ degree N j := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective (relC N) z
  exact ⟨rawDegreeProjection N j u, rawDegreeProjection_mem N j u, rfl⟩

theorem degreeProjection_of_mem {j : ℕ} {z : RelativeChains N} (hz : z ∈ degree N j) :
    degreeProjection N j z = z := by
  obtain ⟨u, hu, rfl⟩ := hz
  rw [degreeProjection_mk, rawDegreeProjection_of_mem N hu]

theorem degreeProjection_of_mem_ne {j q : ℕ} (hjq : j ≠ q) {z : RelativeChains N}
    (hz : z ∈ degree N q) : degreeProjection N j z = 0 := by
  obtain ⟨u, hu, rfl⟩ := hz
  rw [degreeProjection_mk, rawDegreeProjection_of_mem_ne N hjq hu, map_zero]

/-- Projection with codomain restricted to the actual degree group. -/
def degreeComponent (j : ℕ) : RelativeChains N →ₗ[ℂ] degree N j :=
  (degreeProjection N j).codRestrict _ (degreeProjection_mem N j)

@[simp] theorem degreeComponent_val (j : ℕ) (z : RelativeChains N) :
    (degreeComponent N j z).val = degreeProjection N j z := rfl

@[simp] theorem degreeComponent_subtype (j : ℕ) (z : degree N j) :
    degreeComponent N j z = z := by
  apply Subtype.ext
  exact degreeProjection_of_mem N z.property

theorem degreeComponent_subtype_ne {j q : ℕ} (hjq : j ≠ q) (z : degree N q) :
    degreeComponent N j z = 0 := by
  apply Subtype.ext
  exact degreeProjection_of_mem_ne N hjq z.property

end KhanSL2.Factorization
