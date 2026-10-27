module

public import KhanSL2.SymmetricFamily.LocalCoefficients
public import KhanSL2.SymmetricFamily.ColorAnnihilator
public import KhanSL2.Factorization.EvenWeightBoundsInheritance

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The genuine current-submodule displacement filtration of the actual local
symmetric coefficient family. Every successive quotient is an evaluation
module, and the positive filtration has no extremal Cartan vector. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald

/-- To check current stability, it suffices to check the actual root modes. -/
theorem current_lie_mem_of_modes {M : Type*} [AddCommGroup M] [Module ℂ M]
    [LieRingModule BGG.Current M] [LieModule ℂ BGG.Current M]
    (N : Submodule ℂ M) (v : M)
    (h : ∀ n x, ⁅BGG.mode n x,v⁆ ∈ N) (u : BGG.Current) : ⁅u,v⁆ ∈ N := by
  let f : BGG.Current →ₗ[ℂ] M :=
    { toFun := fun x => ⁅x,v⁆
      map_add' := fun x y => add_lie x y v
      map_smul' := fun z x => smul_lie z x v }
  have hspan : Submodule.span ℂ (Set.range BGG.currentBasis) ≤ N.comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨n,c⟩,rfl⟩
    change ⁅BGG.currentBasis (n,c),v⁆ ∈ N
    rw [BGG.currentBasis_apply]
    exact h n (BGG.rootBasis c)
  exact hspan (by rw [BGG.currentBasis.span_eq]; exact Submodule.mem_top)

/-- The displacement filtration as actual current submodules of the original fibre. -/
def localSymmetricFiltration (k : ℕ) (a : ℂ) (d : ℕ) :
    LieSubmodule ℂ BGG.Current (LocalSymmetricFibre k a) where
  __ := (localRootColorFiltration k a d).comap (localSymmetricRootInclusion k a)
  lie_mem {u v} hv := by
    apply current_lie_mem_of_modes
      ((localRootColorFiltration k a d).comap (localSymmetricRootInclusion k a)) v _ u
    intro n x
    change localSymmetricRootInclusion k a ⁅BGG.mode n x,v⁆ ∈ localRootColorFiltration k a d
    rw [localSymmetricRootInclusion_mode]
    exact localRootColorMode_preserves k a n d _ hv

@[simp] theorem mem_localSymmetricFiltration (k : ℕ) (a : ℂ) (d : ℕ)
    (v : LocalSymmetricFibre k a) : v ∈ localSymmetricFiltration k a d ↔
    localSymmetricRootInclusion k a v ∈ localRootColorFiltration k a d := Iff.rfl

@[simp] theorem localSymmetricFiltration_zero (k : ℕ) (a : ℂ) :
    localSymmetricFiltration k a 0 = ⊤ := by
  ext v
  simp only [mem_localSymmetricFiltration, localRootColorFiltration_zero]
  rfl

/-- The actual current filtration is decreasing. -/
theorem localSymmetricFiltration_antitone (k : ℕ) (a : ℂ) :
    Antitone (localSymmetricFiltration k a) := by
  intro d e h v hv
  exact idealTensorSubmodule_mono (Color k) (Ideal.pow_le_pow_right h) hv

/-- The actual current filtration terminates after finitely many steps. -/
theorem localSymmetricFiltration_terminates (k : ℕ) (a : ℂ) :
    ∃ d, localSymmetricFiltration k a d = ⊥ := by
  obtain ⟨d,hd⟩ := localRootColorFiltration_terminates k a
  refine ⟨d,le_antisymm ?_ bot_le⟩
  intro v hv
  have hz : localSymmetricRootInclusion k a v = 0 := by
    change localSymmetricRootInclusion k a v ∈ localRootColorFiltration k a d at hv
    rw [hd] at hv
    exact hv
  change v = 0
  apply localSymmetricRootInclusion_injective k a
  simpa only [map_zero] using hz

/-- The difference between a current mode and its point evaluation raises the filtration. -/
theorem localSymmetricFiltration_deviation (k : ℕ) (a : ℂ) (d n : ℕ)
    (x : BGG.G) {v : LocalSymmetricFibre k a} (hv : v ∈ localSymmetricFiltration k a d) :
    ⁅BGG.mode n x,v⁆ - (a^n) • ⁅BGG.constant x,v⁆ ∈ localSymmetricFiltration k a (d+1) := by
  change localSymmetricRootInclusion k a _ ∈ localRootColorFiltration k a (d+1)
  rw [map_sub,map_smul,localSymmetricRootInclusion_mode,BGG.constant_apply,
    localSymmetricRootInclusion_mode]
  have h := localRootColorDeviation_raises k a n d (LieAlgebra.ad ℂ BGG.G x) hv
  rw [localRootColorDeviation_eq,LinearMap.sub_apply,LinearMap.smul_apply] at h
  exact h

/-- The original constant Cartan action in the local root coordinates. -/
theorem localSymmetricRootInclusion_cartan (k : ℕ) (a : ℂ) (v : LocalSymmetricFibre k a) :
    localSymmetricRootInclusion k a ⁅BGG.constant MatrixSL2.h,v⁆ =
      LinearMap.lTensor (LocalRootAlgebra k a)
        (colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h)) (localSymmetricRootInclusion k a v) := by
  rw [BGG.constant_apply,localSymmetricRootInclusion_mode,localRootColorMode_zero]

/-- The actual local fibre satisfies the finite even Cartan annihilator. -/
theorem localSymmetricCartan_annihilator (k : ℕ) (a : ℂ) :
    Polynomial.aeval
      (LieModule.toEnd ℂ BGG.Current (LocalSymmetricFibre k a) (BGG.constant MatrixSL2.h))
      (Factorization.EvenWeightBounds.evenBoundPolynomial k) = 0 := by
  exact Factorization.EvenWeightBounds.annihilator_of_injective _ _
    (localSymmetricRootInclusion k a) (localSymmetricRootInclusion_injective k a)
    (localSymmetricRootInclusion_cartan k a) _ (rootColorCartan_annihilator k _)

/-- Positive displacement removes the actual extremal weight in the original fibre. -/
theorem localSymmetricFiltration_positive_top_eq_zero (k : ℕ) (a : ℂ)
    (v : LocalSymmetricFibre k a) (hv : v ∈ localSymmetricFiltration k a 1)
    (hcartan : ⁅BGG.constant MatrixSL2.h,v⁆ = (2*(k:ℂ)) • v) : v = 0 := by
  apply localSymmetricRootInclusion_injective k a
  rw [map_zero]
  apply localRootColor_positive_top_eq_zero k a _
    (localSymmetricRootInclusion_invariant k a v) hv
  rw [← localSymmetricRootInclusion_cartan,hcartan,map_smul]

end KhanSL2.SymmetricFamily
