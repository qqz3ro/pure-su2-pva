module

public import KhanSL2.BGG.RootActionEnergy

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Cartan eigenvectors inherit the sharp exterior energy bound. -/

noncomputable section
namespace KhanSL2.BGG

/-- The actual Cartan operator is diagonal in the concrete exterior coefficient functions. -/
theorem rootExteriorAction_h_apply (u : RootExterior) (s : Finset RootMode) :
    rootExteriorAction MatrixSL2.h u s = (2 * (rootMonomialWeight s : ℂ)) * u s := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv, mul_add]
  | single t r =>
    have hr : Finsupp.single t r = r • FiniteExterior.monomial t := by
      simp [FiniteExterior.monomial]
    rw [hr, map_smul, rootExteriorAction_h_monomial]
    simp only [Finsupp.smul_apply, smul_eq_mul, FiniteExterior.monomial, Finsupp.single_apply]
    by_cases h : t = s
    · subst t
      simp
      ring
    · simp [h]

/-- Every nonzero coefficient of a Cartan eigenvector has the specified half-weight. -/
theorem rootMonomialWeight_of_h_eigenvector (u : RootExterior) (j : ℤ)
    (hH : rootExteriorAction MatrixSL2.h u = (2 * (j : ℂ)) • u)
    {s : Finset RootMode} (hs : s ∈ u.support) : rootMonomialWeight s = j := by
  have heq := congrArg (fun v : RootExterior => v s) hH
  rw [rootExteriorAction_h_apply, Finsupp.smul_apply, smul_eq_mul] at heq
  have hmul := mul_right_cancel₀ (Finsupp.mem_support_iff.mp hs) heq
  have hcast := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) hmul
  exact_mod_cast hcast

/-- The representation-theoretic eigenspace is contained in the support-defined weight piece. -/
theorem root_h_eigenvector_mem_weight_piece {d N : ℕ} {u : RootExterior}
    (hu : u ∈ rootExteriorPiece d N) (j : ℤ)
    (hH : rootExteriorAction MatrixSL2.h u = (2 * (j : ℂ)) • u) :
    u ∈ rootWeightEnergyPiece j N := by
  intro s hs
  exact ⟨rootMonomialWeight_of_h_eigenvector u j hH hs, (hu hs).2⟩

/-- A nonzero actual Cartan eigenvector of eigenvalue `2j` has energy at least `j(j+1)/2`. -/
theorem triangular_le_energy_of_h_eigenvector {d N : ℕ} {u : RootExterior}
    (hu : u ∈ rootExteriorPiece d N) (hne : u ≠ 0) (j : ℕ)
    (hH : rootExteriorAction MatrixSL2.h u = (2 * (j : ℂ)) • u) : triangular j ≤ N := by
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hw : rootMonomialWeight s = (j : ℤ) := by
    apply rootMonomialWeight_of_h_eigenvector u j _ hs
    simpa using hH
  have hbound := triangular_le_rootMonomialEnergy s j hw
  simpa only [(hu hs).2] using hbound

/-- Nonnegative integral Cartan eigenvalues in root exterior algebra are even. -/
theorem root_h_eigenvalue_even {u : RootExterior} (hne : u ≠ 0) (n : ℕ)
    (hH : rootExteriorAction MatrixSL2.h u = (n : ℂ) • u) : ∃ j : ℕ, n = 2 * j := by
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hne
  have heq := congrArg (fun v : RootExterior => v s) hH
  rw [rootExteriorAction_h_apply, Finsupp.smul_apply, smul_eq_mul] at heq
  have hcast := mul_right_cancel₀ (Finsupp.mem_support_iff.mp hs) heq
  have hint : 2 * rootMonomialWeight s = (n : ℤ) := by exact_mod_cast hcast
  have hw : 0 ≤ rootMonomialWeight s := by omega
  refine ⟨(rootMonomialWeight s).toNat, ?_⟩
  omega

/-- A highest-weight classification with arbitrary natural weight automatically has weight `2j`
and obeys the triangular energy bound. No highest-weight hypothesis is needed for this bound. -/
theorem root_h_nonnegative_eigenvalue_energy {d N : ℕ} {u : RootExterior}
    (hu : u ∈ rootExteriorPiece d N) (hne : u ≠ 0) (n : ℕ)
    (hH : rootExteriorAction MatrixSL2.h u = (n : ℂ) • u) :
    ∃ j : ℕ, n = 2 * j ∧ triangular j ≤ N := by
  obtain ⟨j, rfl⟩ := root_h_eigenvalue_even hne n hH
  refine ⟨j, rfl, triangular_le_energy_of_h_eigenvector hu hne j ?_⟩
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using hH
/-- At minimum energy, the actual Cartan eigenspace is the single highest wedge line. -/
theorem root_h_eigenvector_minimal_mem_span {d : ℕ} {u : RootExterior} (j : ℕ)
    (hu : u ∈ rootExteriorPiece d (triangular j))
    (hH : rootExteriorAction MatrixSL2.h u = (2 * (j : ℂ)) • u) :
    u ∈ Submodule.span ℂ {FiniteExterior.monomial (RootSupport.highest j).toFinset} := by
  have hw : u ∈ rootWeightEnergyPiece j (triangular j) :=
    root_h_eigenvector_mem_weight_piece hu j (by simpa using hH)
  rwa [rootWeightEnergyPiece_minimal] at hw

/-- A nonzero minimum-energy Cartan eigenvector has exterior degree exactly `j`. -/
theorem root_h_eigenvector_minimal_degree {d : ℕ} {u : RootExterior} (j : ℕ)
    (hu : u ∈ rootExteriorPiece d (triangular j)) (hne : u ≠ 0)
    (hH : rootExteriorAction MatrixSL2.h u = (2 * (j : ℂ)) • u) : d = j := by
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hw : rootMonomialWeight s = (j : ℤ) := by
    apply rootMonomialWeight_of_h_eigenvector u j _ hs
    simpa using hH
  exact (hu hs).1.symm.trans
    (rootMonomial_card_of_minimal_energy s j hw (hu hs).2)

end KhanSL2.BGG