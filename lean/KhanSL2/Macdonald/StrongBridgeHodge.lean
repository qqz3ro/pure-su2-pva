module

public import KhanSL2.StrongMacdonald.Hodge

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! Passing from the proved finite-piece Macdonald Hodge decomposition to
finite-support restricted cochains. No infinite completion is introduced. -/
noncomputable section
namespace KhanSL2.Macdonald

/-- A finite sum of the existing finite-dimensional weight/degree pieces. -/
def strongFiniteWindow (N : ℕ) : Submodule ℂ StrongMacdonald.W :=
  ⨆ w : Fin (N+1), ⨆ s : Fin (N+1), StrongMacdonald.piece w.val s.val

instance strongFiniteWindow_finiteDimensional (N : ℕ) :
    FiniteDimensional ℂ (strongFiniteWindow N) := by
  unfold strongFiniteWindow
  infer_instance

theorem strongPiece_le_window (N w s : ℕ) (hw : w ≤ N) (hs : s ≤ N) :
    StrongMacdonald.piece w s ≤ strongFiniteWindow N :=
  le_trans (le_iSup_of_le (⟨s,by omega⟩ : Fin (N+1)) le_rfl)
    (le_iSup_of_le (⟨w,by omega⟩ : Fin (N+1)) le_rfl)

theorem strongFiniteWindow_mono {N M : ℕ} (h : N ≤ M) :
    strongFiniteWindow N ≤ strongFiniteWindow M := by
  apply iSup_le
  intro w
  apply iSup_le
  intro s
  exact strongPiece_le_window M w.val s.val (by omega) (by omega)

theorem strong_mem_finiteWindow (u : StrongMacdonald.W) :
    ∃ N, u ∈ strongFiniteWindow N := by
  refine StrongMacdonald.mono_induction (P := fun u => ∃ N, u ∈ strongFiniteWindow N)
    ?_ ?_ ?_ ?_ u
  · exact ⟨0, Submodule.zero_mem _⟩
  · rintro x y ⟨N,hN⟩ ⟨M,hM⟩
    exact ⟨max N M, Submodule.add_mem _
      (strongFiniteWindow_mono (le_max_left _ _) hN)
      (strongFiniteWindow_mono (le_max_right _ _) hM)⟩
  · rintro c x ⟨N,hN⟩
    exact ⟨N, Submodule.smul_mem _ c hN⟩
  · intro e t
    exact ⟨max (StrongMacdonald.wtVal e t) (StrongMacdonald.sdVal e t),
      strongPiece_le_window _ _ _ (le_max_left _ _) (le_max_right _ _)
        (StrongMacdonald.mono_mem_piece e t)⟩

theorem strongFiniteWindow_stable (N : ℕ) (D : Module.End ℂ StrongMacdonald.W)
    (hD : ∀ w s u, u ∈ StrongMacdonald.piece w s → D u ∈ StrongMacdonald.piece w s) :
    strongFiniteWindow N ≤ (strongFiniteWindow N).comap D := by
  apply iSup_le
  intro w
  apply iSup_le
  intro s u hu
  exact strongPiece_le_window N w.val s.val (by omega) (by omega) (hD _ _ _ hu)

/-- Every restricted invariant cocycle has a harmonic representative. This is
an application of the already proved Hodge theorem on a finite stable window. -/
theorem strong_exists_harm_add_dbar {z : StrongMacdonald.W} (hz : z ∈ StrongMacdonald.inv)
    (hdz : StrongMacdonald.dbar z = 0) :
    ∃ h ∈ StrongMacdonald.harm, ∃ u ∈ StrongMacdonald.inv, z = h + StrongMacdonald.dbar u := by
  obtain ⟨N,hN⟩ := strong_mem_finiteWindow z
  let V := strongFiniteWindow N ⊓ StrongMacdonald.inv
  have : FiniteDimensional ℂ V := Submodule.finiteDimensional_of_le inf_le_left
  have hd : ∀ u ∈ V, StrongMacdonald.dbar u ∈ V := by
    intro u hu
    exact ⟨strongFiniteWindow_stable N _
      (fun _ _ _ h => StrongMacdonald.mapsTo_piece StrongMacdonald.Wt_comm_dbar
        StrongMacdonald.Sd_comm_dbar h) hu.1, StrongMacdonald.dbar_mem_inv hu.2⟩
  have hdd : ∀ u ∈ V, StrongMacdonald.dbarDag u ∈ V := by
    intro u hu
    exact ⟨strongFiniteWindow_stable N _
      (fun _ _ _ h => StrongMacdonald.mapsTo_piece StrongMacdonald.Wt_comm_dbarDag
        StrongMacdonald.Sd_comm_dbarDag h) hu.1, StrongMacdonald.dbarDag_mem_inv hu.2⟩
  obtain ⟨h,hh,hdh,hddh,u,hu,he⟩ := StrongMacdonald.exists_harmonic_add_d
    (V := V) StrongMacdonald.isAdj_dbar hd hdd
    (fun u _ => StrongMacdonald.dbar_dbar_apply u) ⟨hN,hz⟩ hdz
  exact ⟨h, StrongMacdonald.mem_harm.mpr ⟨hh.2,hdh,hddh⟩,u,hu.2,he⟩

end KhanSL2.Macdonald
