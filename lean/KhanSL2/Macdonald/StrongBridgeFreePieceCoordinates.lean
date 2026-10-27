module

public import KhanSL2.Macdonald.StrongBridgeFreePieces
public import KhanSL2.Macdonald.StrongBridgeFreeIndices

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The finite free Macdonald pieces have specified monomial bases, indexed by
actual loop weight and coefficient degree. -/
noncomputable section
namespace KhanSL2.Macdonald

theorem strong_diag_eigen_support (a : StrongMacdonald.SMode → ℕ)
    (b : StrongMacdonald.PMode → ℕ) (n : ℕ) (u : StrongMacdonald.W) :
    StrongMacdonald.diagDer a b u = (n : ℂ) • u ↔
      ∀ e t, StrongMacdonald.coefW u e t ≠ 0 → StrongMacdonald.diagVal a b e t = n := by
  constructor
  · intro hu e t hc
    have he := StrongMacdonald.coefW_diagDer a b u e t
    rw [hu, StrongMacdonald.coefW_smul] at he
    exact_mod_cast (mul_right_cancel₀ hc he).symm
  · intro h
    apply AddMonoidAlgebra.coeff_injective
    ext e t
    change StrongMacdonald.coefW (StrongMacdonald.diagDer a b u) e t =
      StrongMacdonald.coefW ((n : ℂ) • u) e t
    rw [StrongMacdonald.coefW_diagDer, StrongMacdonald.coefW_smul]
    by_cases hc : StrongMacdonald.coefW u e t = 0
    · simp [hc]
    · rw [h e t hc]

def strongFreePieceIndices (w s : ℕ) : Set StrongMonomialIndex :=
  {b | b ∈ strongFreeIndices ∧ StrongMacdonald.wtVal b.1 b.2 = w ∧
    StrongMacdonald.diagVal (fun _ => 2) (fun _ => 1) b.1 b.2 = s}

theorem strongCoordinates_supportedPiece (w s : ℕ) (u : StrongMacdonald.W) :
    strongCoordinates u ∈ Finsupp.supported ℂ ℂ (strongFreePieceIndices w s) ↔
      u ∈ strongFreePiece w s := by
  rw [mem_strongFreePiece]
  constructor
  · intro hu
    refine ⟨(strongCoordinates_supported u).mp (fun b hb => (hu hb).1), ?_, ?_⟩
    · apply (strong_diag_eigen_support _ _ w u).mpr
      intro e t hc
      exact (hu (show (e,t) ∈ (strongCoordinates u).support from
        Finsupp.mem_support_iff.mpr hc)).2.1
    · apply (strong_diag_eigen_support _ _ s u).mpr
      intro e t hc
      exact (hu (show (e,t) ∈ (strongCoordinates u).support from
        Finsupp.mem_support_iff.mpr hc)).2.2
  · rintro ⟨hp,hw,hs⟩ b hb
    obtain ⟨e,t⟩ := b
    have hc := Finsupp.mem_support_iff.mp hb
    change StrongMacdonald.coefW u e t ≠ 0 at hc
    exact ⟨(strongCoordinates_supported u).mpr hp hb,
      (strong_diag_eigen_support _ _ w u).mp hw e t hc,
      (strong_diag_eigen_support _ _ s u).mp hs e t hc⟩

def strongFreePieceSupportedEquiv (w s : ℕ) :
    strongFreePiece w s ≃ₗ[ℂ] Finsupp.supported ℂ ℂ (strongFreePieceIndices w s) :=
  (strongCoordinates.submoduleMap (strongFreePiece w s)).trans
    (LinearEquiv.ofEq _ _ (by
      ext x
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact (strongCoordinates_supportedPiece w s u).mpr hu
      · intro hx
        refine ⟨strongCoordinates.symm x, ?_, strongCoordinates.apply_symm_apply x⟩
        apply (strongCoordinates_supportedPiece w s _).mp
        simpa using hx))

/-- The exact finite-coordinate basis of the source for each actual homology block. -/
def strongFreePieceCoordinateEquiv (w s : ℕ) :
    strongFreePiece w s ≃ₗ[ℂ] (strongFreePieceIndices w s) →₀ ℂ :=
  (strongFreePieceSupportedEquiv w s).trans
    (Finsupp.supportedEquivFinsupp (strongFreePieceIndices w s))

@[simp] theorem strongFreePieceCoordinateEquiv_apply (w s : ℕ)
    (u : strongFreePiece w s) (b : strongFreePieceIndices w s) :
    strongFreePieceCoordinateEquiv w s u b = StrongMacdonald.coefW u.val b.val.1 b.val.2 := rfl

instance strongFreePiece_finiteDimensional (w s : ℕ) : FiniteDimensional ℂ (strongFreePiece w s) := by
  have : FiniteDimensional ℂ ↥(StrongMacdonald.harm ⊓ StrongMacdonald.piece w s) :=
    Submodule.finiteDimensional_of_le inf_le_right
  exact LinearEquiv.finiteDimensional (strongFreePieceHarmonicEquiv w s).symm

instance strongFreePieceIndices_finite (w s : ℕ) : Finite (strongFreePieceIndices w s) := by
  have : FiniteDimensional ℂ ((strongFreePieceIndices w s) →₀ ℂ) :=
    LinearEquiv.finiteDimensional (strongFreePieceCoordinateEquiv w s)
  exact Module.Finite.finite_basis (Finsupp.basisSingleOne :
    Module.Basis (strongFreePieceIndices w s) ℂ ((strongFreePieceIndices w s) →₀ ℂ))

end KhanSL2.Macdonald
