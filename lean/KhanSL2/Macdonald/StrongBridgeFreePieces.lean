module

public import KhanSL2.Macdonald.StrongBridgeFreeCoordinates
public import KhanSL2.Macdonald.StrongBridgeFreeGrading

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The specified free-generator isomorphism restricts to the actual finite
weight and coefficient-degree pieces. The source degrees are explicit. -/
noncomputable section
namespace KhanSL2.Macdonald

/-- A linear eigenspace, including its zero vector. -/
def strongEigen (D : Module.End ℂ StrongMacdonald.W) (c : ℂ) : Submodule ℂ StrongMacdonald.W :=
  LinearMap.ker (D - c • LinearMap.id)

@[simp] theorem mem_strongEigen (D : Module.End ℂ StrongMacdonald.W) (c : ℂ)
    (u : StrongMacdonald.W) : u ∈ strongEigen D c ↔ D u = c • u := by
  simp [strongEigen, LinearMap.mem_ker, sub_eq_zero]

/-- In the free source, even generators count twice and odd generators once. -/
def strongFreePiece (w s : ℕ) : Submodule ℂ StrongMacdonald.W :=
  strongFree ⊓ (strongEigen StrongMacdonald.Wt (w : ℂ) ⊓
    strongEigen strongFreeSymmetricEuler (s : ℂ))

theorem mem_strongFreePiece (w s : ℕ) (u : StrongMacdonald.W) :
    u ∈ strongFreePiece w s ↔ StrongMacdonald.projFull u = u ∧
      StrongMacdonald.Wt u = (w : ℂ) • u ∧ strongFreeSymmetricEuler u = (s : ℂ) • u := by
  simp only [strongFreePiece, Submodule.mem_inf, mem_strongEigen]
  rfl

/-- Injectivity of the actual free-generator map reflects diagonal eigenvalues. -/
theorem strong_Gmap_reflect_eigen
    (a : StrongMacdonald.SMode → ℕ) (b : StrongMacdonald.PMode → ℕ)
    (T : Module.End ℂ StrongMacdonald.W)
    (hT : ∀ u, T (StrongMacdonald.Gmap u) =
      StrongMacdonald.Gmap (StrongMacdonald.diagDer a b u))
    {u : StrongMacdonald.W} (hu : StrongMacdonald.projFull u = u) (c : ℂ)
    (he : T (StrongMacdonald.Gmap u) = c • StrongMacdonald.Gmap u) :
    StrongMacdonald.diagDer a b u = c • u := by
  apply sub_eq_zero.mp
  apply StrongMacdonald.Gmap_injOn
  · rw [map_sub, map_smul, ← strong_diagDer_projFull, hu]
  · rw [map_sub, map_smul, ← hT, he, sub_self]

/-- Restrict Gmap itself, retaining its normalization, to a finite homogeneous source. -/
def strongFreePieceToHarmonic (w s : ℕ) :
    strongFreePiece w s →ₗ[ℂ] ↥(StrongMacdonald.harm ⊓ StrongMacdonald.piece w s) where
  toFun u := ⟨StrongMacdonald.Gmap u.val, by
    obtain ⟨_hu,hw,hs⟩ := (mem_strongFreePiece w s u.val).mp u.property
    refine ⟨StrongMacdonald.Gmap_mem_harm u.val, ?_, ?_⟩
    · rw [strong_Wt_Gmap, hw, map_smul]
    · rw [strong_Sd_Gmap, hs, map_smul]⟩
  map_add' u v := by apply Subtype.ext; exact map_add StrongMacdonald.Gmap u.val v.val
  map_smul' c u := by apply Subtype.ext; exact map_smul StrongMacdonald.Gmap c u.val

theorem strongFreePieceToHarmonic_bijective (w s : ℕ) :
    Function.Bijective (strongFreePieceToHarmonic w s) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact StrongMacdonald.Gmap_injOn
      ((mem_strongFreePiece w s u.val).mp u.property).1
      (congrArg Subtype.val (LinearMap.mem_ker.mp hu))
  · intro h
    obtain ⟨u,hu,he⟩ := StrongMacdonald.exists_free_preimage h.property.1
    have hw : StrongMacdonald.Wt u = (w : ℂ) • u :=
      strong_Gmap_reflect_eigen (fun g => g.index) (fun g => g.index+1)
        StrongMacdonald.Wt strong_Wt_Gmap hu (w : ℂ) (by rw [he]; exact h.property.2.1)
    have hs : strongFreeSymmetricEuler u = (s : ℂ) • u :=
      strong_Gmap_reflect_eigen (fun _ => 2) (fun _ => 1)
        StrongMacdonald.Sd strong_Sd_Gmap hu (s : ℂ) (by rw [he]; exact h.property.2.2)
    exact ⟨⟨u,(mem_strongFreePiece w s u).mpr ⟨hu,hw,hs⟩⟩, Subtype.ext he⟩

/-- The finite graded form of the already proved Macdonald harmonic theorem. -/
def strongFreePieceHarmonicEquiv (w s : ℕ) :
    strongFreePiece w s ≃ₗ[ℂ] ↥(StrongMacdonald.harm ⊓ StrongMacdonald.piece w s) :=
  LinearEquiv.ofBijective (strongFreePieceToHarmonic w s)
    (strongFreePieceToHarmonic_bijective w s)

end KhanSL2.Macdonald
