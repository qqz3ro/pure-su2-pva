module

public import KhanSL2.StrongMacdonald.Harmonic
public import KhanSL2.StrongMacdonald.DbarSquare
public import KhanSL2.StrongMacdonald.Grading
public import KhanSL2.StrongMacdonald.HodgeAbstract

@[expose] public section

/-!
# Hodge theory on the invariant complex (FGT, step A4)

The invariant complex `C = W^𝔤` splits into finite-dimensional pieces `C(w,s)` of loop weight
`w` and σ-degree `s`, each preserved by `∂̄` and `∂̄†`. On each piece every cocycle is uniquely
harmonic plus a coboundary, so the cohomology of `C(w,s)` is isomorphic to the harmonic
invariants of bidegree `(w,s)`; by `mem_harm_iff` these are the invariants killed by all
`X_a(m)` and `d_a(-m)†`.
-/

noncomputable section
open scoped BigOperators

namespace KhanSL2.StrongMacdonald

/-- The piece `C(w,s)` of the invariant complex. -/
def invPiece (w s : ℕ) : Submodule ℂ W := piece w s ⊓ inv

instance (w s : ℕ) : FiniteDimensional ℂ (invPiece w s) :=
  Submodule.finiteDimensional_of_le inf_le_left

theorem dbar_mem_invPiece {w s : ℕ} {x : W} (hx : x ∈ invPiece w s) : dbar x ∈ invPiece w s :=
  ⟨mapsTo_piece Wt_comm_dbar Sd_comm_dbar hx.1, dbar_mem_inv hx.2⟩

theorem dbarDag_mem_invPiece {w s : ℕ} {x : W} (hx : x ∈ invPiece w s) :
    dbarDag x ∈ invPiece w s :=
  ⟨mapsTo_piece Wt_comm_dbarDag Sd_comm_dbarDag hx.1, dbarDag_mem_inv hx.2⟩

/-- Hodge decomposition of invariant cocycles. -/
theorem exists_harm_add_dbar {w s : ℕ} {z : W} (hz : z ∈ invPiece w s) (hdz : dbar z = 0) :
    ∃ h ∈ harm ⊓ piece w s, ∃ u ∈ invPiece w s, z = h + dbar u := by
  obtain ⟨h, hV, hh1, hh2, u, hu, rfl⟩ := exists_harmonic_add_d isAdj_dbar
    (fun x hx => dbar_mem_invPiece hx) (fun x hx => dbarDag_mem_invPiece hx)
    (fun x _ => dbar_dbar_apply x) hz hdz
  exact ⟨h, ⟨mem_harm.mpr ⟨hV.2, hh1, hh2⟩, hV.1⟩, u, hu, rfl⟩

/-- A harmonic coboundary vanishes. -/
theorem eq_zero_of_mem_harm_of_eq_dbar {h u : W} (hh : h ∈ harm) (hu : h = dbar u) : h = 0 :=
  eq_zero_of_dd_eq_zero_of_eq_d isAdj_dbar (mem_harm.mp hh).2.2 hu

/-! ## Cohomology of a piece -/

/-- Cocycles of `C(w,s)`. -/
def cocyc (w s : ℕ) : Submodule ℂ W := invPiece w s ⊓ LinearMap.ker dbar

/-- Coboundaries of `C(w,s)`. -/
def cobd (w s : ℕ) : Submodule ℂ W := (invPiece w s).map dbar

theorem cobd_le_cocyc (w s : ℕ) : cobd w s ≤ cocyc w s := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨dbar_mem_invPiece hu, by simp [dbar_dbar_apply]⟩

/-- The cohomology `H(C(w,s))`. -/
abbrev cohom (w s : ℕ) : Type := cocyc w s ⧸ (cobd w s).comap (cocyc w s).subtype

theorem harm_inf_piece_le_cocyc (w s : ℕ) : harm ⊓ piece w s ≤ cocyc w s := by
  rintro x ⟨hx, hp⟩
  obtain ⟨hinv, hd, -⟩ := mem_harm.mp hx
  exact ⟨⟨hp, hinv⟩, hd⟩

/-- Harmonic invariants map to cohomology classes. -/
def harmToCohom (w s : ℕ) : (harm ⊓ piece w s : Submodule ℂ W) →ₗ[ℂ] cohom w s :=
  (Submodule.mkQ _).comp (Submodule.inclusion (harm_inf_piece_le_cocyc w s))

theorem harmToCohom_bijective (w s : ℕ) : Function.Bijective (harmToCohom w s) := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨h, hh⟩ hk
    rw [LinearMap.mem_ker, harmToCohom, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hk
    obtain ⟨u, -, hu⟩ := hk
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact eq_zero_of_mem_harm_of_eq_dbar hh.1 hu.symm
  · intro c
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨h, hh, u, hu, rfl⟩ := exists_harm_add_dbar hz.1 hz.2
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [harmToCohom, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.eq,
      Submodule.mem_comap]
    refine ⟨-u, neg_mem hu, ?_⟩
    simp

/-- FGT step A4: the cohomology of the invariant complex in bidegree `(w,s)` is the space of
harmonic invariants of that bidegree. -/
def harmEquivCohom (w s : ℕ) : (harm ⊓ piece w s : Submodule ℂ W) ≃ₗ[ℂ] cohom w s :=
  LinearEquiv.ofBijective (harmToCohom w s) (harmToCohom_bijective w s)

end KhanSL2.StrongMacdonald
