module

public import KhanSL2.BGG.PositiveLaplacian
public import KhanSL2.BGG.PositiveSpectralKernel
public import KhanSL2.BGG.PositiveCEGrading
public import KhanSL2.BGG.GradedKernel

@[expose] public section
noncomputable section
open scoped BigOperators
open KhanSL2.FiniteExterior
namespace KhanSL2.BGG.PositiveCE

/-- The concrete Laplacian preserves exterior degree and physical energy. -/
theorem laplacian_mem_piece {p N : ℕ} {u : Cochain} (hu : u ∈ piece p N) :
    laplacian u ∈ piece p N := by
  rw [laplacian_eq_energyCasimir, energyCasimir_coe_piece p N (⟨u,hu⟩ : liePiece p N)]
  exact (spectralOperator p N ⟨u,hu⟩).property

/-- A harmonic cochain in a nonexceptional bidegree vanishes. -/
theorem eq_zero_of_laplacian_eq_zero_of_energy_ne {p N : ℕ} {u : Cochain}
    (hu : u ∈ piece p N) (hL : laplacian u = 0) (hN : N ≠ triangular p) : u = 0 := by
  let v : liePiece p N := ⟨u,hu⟩
  have hv : v ∈ spectralKernel p N := by
    change spectralOperator p N v = 0
    apply Subtype.ext
    change (spectralOperator p N v : Cochain) = 0
    rw [← energyCasimir_coe_piece, ← laplacian_eq_energyCasimir]
    exact hL
  rw [spectralKernel_eq_bot_of_energy_ne hN] at hv
  have hz : v = 0 := by simpa using hv
  exact congrArg Subtype.val hz

private theorem d_harmonic_piece {p N : ℕ} {u : Cochain}
    (hu : u ∈ piece p N) (hL : laplacian u = 0) : d u = 0 := by
  by_cases hN : N = triangular p
  · apply eq_zero_of_laplacian_eq_zero_of_energy_ne (d_mem_piece hu)
    · rw [laplacian_d, hL, map_zero]
    · rw [hN]
      exact ne_of_lt (triangular_strictMono (Nat.lt_succ_self p))
  · rw [eq_zero_of_laplacian_eq_zero_of_energy_ne hu hL hN, map_zero]

private theorem boundary_degree_zero {N : ℕ} {u : Cochain} (hu : u ∈ piece 0 N) :
    boundary u = 0 := by
  rw [eq_sum_support u]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro s hs
  have hs0 : s = ∅ := Finset.card_eq_zero.mp (hu hs).1
  subst s
  change u ∅ • boundary 1 = 0
  rw [boundary_one, smul_zero]

private theorem boundary_harmonic_piece {p N : ℕ} {u : Cochain}
    (hu : u ∈ piece p N) (hL : laplacian u = 0) : boundary u = 0 := by
  cases p with
  | zero => exact boundary_degree_zero hu
  | succ p =>
    by_cases hN : N = triangular (p+1)
    · apply eq_zero_of_laplacian_eq_zero_of_energy_ne (boundary_mem_piece hu)
      · rw [laplacian_boundary, hL, map_zero]
      · rw [hN]
        exact ne_of_gt (triangular_strictMono (Nat.lt_succ_self p))
    · rw [eq_zero_of_laplacian_eq_zero_of_energy_ne hu hL hN, map_zero]

private theorem basisPiece_eq_piece (p N : ℕ) :
    BasisGrading.piece (fun s : Finset Mode => (s.card,monomialEnergy s)) (p,N) = piece p N := by
  unfold BasisGrading.piece piece
  congr 1
  ext s
  simp only [Set.mem_setOf_eq, Prod.mk.injEq]

/-- The coboundary annihilates every actual harmonic cochain. -/
theorem d_eq_zero_of_laplacian_eq_zero {u : Cochain} (hu : laplacian u = 0) : d u = 0 := by
  apply BasisGrading.map_eq_zero_of_ker_piece
    (fun s : Finset Mode => (s.card,monomialEnergy s)) laplacian d ?_ ?_ hu
  · rintro ⟨p,N⟩ v hv
    rw [basisPiece_eq_piece] at hv ⊢
    exact laplacian_mem_piece hv
  · rintro ⟨p,N⟩ v hv hL
    rw [basisPiece_eq_piece] at hv
    exact d_harmonic_piece hv hL

/-- The homology boundary also annihilates every actual harmonic cochain. -/
theorem boundary_eq_zero_of_laplacian_eq_zero {u : Cochain} (hu : laplacian u = 0) :
    boundary u = 0 := by
  apply BasisGrading.map_eq_zero_of_ker_piece
    (fun s : Finset Mode => (s.card,monomialEnergy s)) laplacian boundary ?_ ?_ hu
  · rintro ⟨p,N⟩ v hv
    rw [basisPiece_eq_piece] at hv ⊢
    exact laplacian_mem_piece hv
  · rintro ⟨p,N⟩ v hv hL
    rw [basisPiece_eq_piece] at hv
    exact boundary_harmonic_piece hv hL

end KhanSL2.BGG.PositiveCE