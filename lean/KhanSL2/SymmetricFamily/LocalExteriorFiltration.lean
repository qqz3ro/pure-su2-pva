module

public import KhanSL2.SymmetricFamily.LocalExteriorCoefficients
public import KhanSL2.SymmetricFamily.LocalFiltration
public import KhanSL2.Factorization.EvenWeightBoundsInheritance

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The genuine current-submodule displacement filtration of the actual local
exterior coefficient family. Every successive quotient is an evaluation
module. -/

noncomputable section
namespace KhanSL2.SymmetricFamily
open PolynomialBGG Macdonald

/-- The displacement filtration as actual current submodules of the original fibre. -/
def localExteriorFiltration (k : ℕ) (a : ℂ) (d : ℕ) :
    LieSubmodule ℂ BGG.Current (LocalExteriorFibre k a) where
  __ := (localRootColorFiltration k a d).comap (localExteriorRootInclusion k a)
  lie_mem {u v} hv := by
    apply current_lie_mem_of_modes
      ((localRootColorFiltration k a d).comap (localExteriorRootInclusion k a)) v _ u
    intro n x
    change localExteriorRootInclusion k a ⁅BGG.mode n x,v⁆ ∈ localRootColorFiltration k a d
    rw [localExteriorRootInclusion_mode]
    exact localRootColorMode_preserves k a n d _ hv

@[simp] theorem mem_localExteriorFiltration (k : ℕ) (a : ℂ) (d : ℕ)
    (v : LocalExteriorFibre k a) : v ∈ localExteriorFiltration k a d ↔
    localExteriorRootInclusion k a v ∈ localRootColorFiltration k a d := Iff.rfl

@[simp] theorem localExteriorFiltration_zero (k : ℕ) (a : ℂ) :
    localExteriorFiltration k a 0 = ⊤ := by
  ext v
  simp only [mem_localExteriorFiltration, localRootColorFiltration_zero]
  rfl

/-- The actual current filtration is decreasing. -/
theorem localExteriorFiltration_antitone (k : ℕ) (a : ℂ) :
    Antitone (localExteriorFiltration k a) := by
  intro d e h v hv
  exact idealTensorSubmodule_mono (Color k) (Ideal.pow_le_pow_right h) hv

/-- The actual current filtration terminates after finitely many steps. -/
theorem localExteriorFiltration_terminates (k : ℕ) (a : ℂ) :
    ∃ d, localExteriorFiltration k a d = ⊥ := by
  obtain ⟨d,hd⟩ := localRootColorFiltration_terminates k a
  refine ⟨d,le_antisymm ?_ bot_le⟩
  intro v hv
  have hz : localExteriorRootInclusion k a v = 0 := by
    change localExteriorRootInclusion k a v ∈ localRootColorFiltration k a d at hv
    rw [hd] at hv
    exact hv
  change v = 0
  apply localExteriorRootInclusion_injective k a
  simpa only [map_zero] using hz

/-- The difference between a current mode and its point evaluation raises the filtration. -/
theorem localExteriorFiltration_deviation (k : ℕ) (a : ℂ) (d n : ℕ)
    (x : BGG.G) {v : LocalExteriorFibre k a} (hv : v ∈ localExteriorFiltration k a d) :
    ⁅BGG.mode n x,v⁆ - (a^n) • ⁅BGG.constant x,v⁆ ∈ localExteriorFiltration k a (d+1) := by
  change localExteriorRootInclusion k a _ ∈ localRootColorFiltration k a (d+1)
  rw [map_sub,map_smul,localExteriorRootInclusion_mode,BGG.constant_apply,
    localExteriorRootInclusion_mode]
  have h := localRootColorDeviation_raises k a n d (LieAlgebra.ad ℂ BGG.G x) hv
  rw [localRootColorDeviation_eq,LinearMap.sub_apply,LinearMap.smul_apply] at h
  exact h

/-- The original constant Cartan action in the local root coordinates. -/
theorem localExteriorRootInclusion_cartan (k : ℕ) (a : ℂ) (v : LocalExteriorFibre k a) :
    localExteriorRootInclusion k a ⁅BGG.constant MatrixSL2.h,v⁆ =
      LinearMap.lTensor (LocalRootAlgebra k a)
        (colorDeriv k (LieAlgebra.ad ℂ BGG.G MatrixSL2.h)) (localExteriorRootInclusion k a v) := by
  rw [BGG.constant_apply,localExteriorRootInclusion_mode,localRootColorMode_zero]

/-- The actual local fibre satisfies the finite even Cartan annihilator. -/
theorem localExteriorCartan_annihilator (k : ℕ) (a : ℂ) :
    Polynomial.aeval
      (LieModule.toEnd ℂ BGG.Current (LocalExteriorFibre k a) (BGG.constant MatrixSL2.h))
      (Factorization.EvenWeightBounds.evenBoundPolynomial k) = 0 := by
  exact Factorization.EvenWeightBounds.annihilator_of_injective _ _
    (localExteriorRootInclusion k a) (localExteriorRootInclusion_injective k a)
    (localExteriorRootInclusion_cartan k a) _ (rootColorCartan_annihilator k _)

end KhanSL2.SymmetricFamily
