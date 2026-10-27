module

public import KhanSL2.BGG.RootExterior
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section

/-! The least-energy, nonnegative-weight space is the single highest wedge line. -/

noncomputable section
namespace KhanSL2.BGG

/-- The monomial-supported subspace of prescribed half-Cartan weight and energy. -/
def rootWeightEnergyPiece (j : ℤ) (N : ℕ) : Submodule ℂ RootExterior :=
  Finsupp.supported ℂ ℂ {s | rootMonomialWeight s = j ∧ rootMonomialEnergy s = N}

/-- No exterior vector has nonnegative half-weight `j` below triangular energy. -/
theorem rootWeightEnergyPiece_eq_bot (j N : ℕ) (hN : N < triangular j) :
    rootWeightEnergyPiece j N = ⊥ := by
  have hset : {s : Finset RootMode | rootMonomialWeight s = (j : ℤ) ∧
      rootMonomialEnergy s = N} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have hbound := triangular_le_rootMonomialEnergy s j hs.1
    rw [hs.2] at hbound
    omega
  simp [rootWeightEnergyPiece, hset, Finsupp.supported_eq_span_single]

/-- At minimum energy, the entire weight space is spanned by `e₁∧...∧eⱼ`. -/
theorem rootWeightEnergyPiece_minimal (j : ℕ) :
    rootWeightEnergyPiece j (triangular j) =
      Submodule.span ℂ {FiniteExterior.monomial (RootSupport.highest j).toFinset} := by
  have hset : {s : Finset RootMode | rootMonomialWeight s = (j : ℤ) ∧
      rootMonomialEnergy s = triangular j} = {(RootSupport.highest j).toFinset} := by
    ext s
    change (_ ∧ _) ↔ s = (RootSupport.highest j).toFinset
    constructor
    · rintro ⟨hw, he⟩
      exact rootMonomial_eq_highest_of_minimal_energy s j hw he
    · rintro rfl
      simp
  simp [rootWeightEnergyPiece, hset, Finsupp.supported_eq_span_single,
    FiniteExterior.monomial]

/-- Minimum energy also fixes the exterior degree. -/
theorem rootMonomial_card_of_minimal_energy (s : Finset RootMode) (j : ℕ)
    (hw : rootMonomialWeight s = j) (he : rootMonomialEnergy s = triangular j) :
    s.card = j := by
  rw [rootMonomial_eq_highest_of_minimal_energy s j hw he,
    RootSupport.card_toFinset, RootSupport.highest_degree]

/-- The minimum-energy weight space lies entirely in exterior degree `j`. -/
theorem rootWeightEnergyPiece_minimal_degree (j : ℕ) :
    rootWeightEnergyPiece j (triangular j) ≤
      Finsupp.supported ℂ ℂ {s : Finset RootMode | s.card = j} := by
  intro u hu s hs
  have h := hu hs
  exact rootMonomial_card_of_minimal_energy s j h.1 h.2
/-- The minimum-energy generator is nonzero in the concrete exterior algebra. -/
theorem rootHighestMonomial_ne_zero (j : ℕ) :
    FiniteExterior.monomial (RootSupport.highest j).toFinset ≠ 0 := by
  simp [FiniteExterior.monomial]

end KhanSL2.BGG