module

public import KhanSL2.Macdonald.StrongBridgeCohomology
public import Mathlib.LinearAlgebra.Finsupp.Supported

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Explicit finite coordinates on the colour-zero free Macdonald algebra.
The equivalence is coefficient evaluation, not a choice of an abstract basis. -/
noncomputable section
namespace KhanSL2.Macdonald

abbrev StrongMonomialIndex := StrongMacdonald.Exp × Finset Mode

/-- Flatten polynomial and exterior coordinates into one finitely supported function. -/
def strongCoordinates : StrongMacdonald.W ≃ₗ[ℂ] StrongMonomialIndex →₀ ℂ :=
  (AddMonoidAlgebra.coeffLinearEquiv ℂ).trans (Finsupp.curryLinearEquiv ℂ).symm

@[simp] theorem strongCoordinates_apply (u : StrongMacdonald.W) (e : StrongMacdonald.Exp)
    (t : Finset Mode) : strongCoordinates u (e,t) = StrongMacdonald.coefW u e t := rfl

/-- Precisely the monomials using only colour-zero generators. -/
def strongFreeIndices : Set StrongMonomialIndex :=
  {b | (∀ g ∈ b.1.support, g.color = 0) ∧ (∀ m ∈ b.2, m.color = 0)}

theorem strongCoordinates_supported (u : StrongMacdonald.W) :
    strongCoordinates u ∈ Finsupp.supported ℂ ℂ strongFreeIndices ↔
      StrongMacdonald.projFull u = u := by
  constructor
  · intro hu
    apply AddMonoidAlgebra.coeff_injective
    ext e t
    change StrongMacdonald.coefW (StrongMacdonald.projFull u) e t =
      StrongMacdonald.coefW u e t
    rw [StrongMacdonald.projFull, StrongMacdonald.coefW_proj]
    by_cases hc : StrongMacdonald.coefW u e t = 0
    · simp [hc]
    · have hm := hu (show (e,t) ∈ (strongCoordinates u).support from
        Finsupp.mem_support_iff.mpr hc)
      exact if_pos hm
  · intro hu b hb
    obtain ⟨e,t⟩ := b
    have hc := Finsupp.mem_support_iff.mp hb
    change StrongMacdonald.coefW u e t ≠ 0 at hc
    have he := congrArg (fun v => StrongMacdonald.coefW v e t) hu
    rw [StrongMacdonald.projFull, StrongMacdonald.coefW_proj] at he
    by_contra hn
    change ¬((∀ g ∈ e.support, g.color = 0) ∧ ∀ m ∈ t, m.color = 0) at hn
    rw [if_neg hn] at he
    exact hc he.symm

/-- Coefficients give exactly the supported-coordinate model of the free algebra. -/
def strongFreeSupportedEquiv : strongFree ≃ₗ[ℂ] Finsupp.supported ℂ ℂ strongFreeIndices :=
  (strongCoordinates.submoduleMap strongFree).trans
    (LinearEquiv.ofEq _ _ (by
      ext x
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact (strongCoordinates_supported u).mpr hu
      · intro hx
        refine ⟨strongCoordinates.symm x, ?_, strongCoordinates.apply_symm_apply x⟩
        change StrongMacdonald.projFull (strongCoordinates.symm x) = strongCoordinates.symm x
        apply (strongCoordinates_supported _).mp
        simpa using hx))

/-- The free harmonic generators have their explicit colour-zero monomial coordinates. -/
def strongFreeCoordinateEquiv : strongFree ≃ₗ[ℂ] strongFreeIndices →₀ ℂ :=
  strongFreeSupportedEquiv.trans (Finsupp.supportedEquivFinsupp strongFreeIndices)

@[simp] theorem strongFreeCoordinateEquiv_apply (u : strongFree) (b : strongFreeIndices) :
    strongFreeCoordinateEquiv u b = StrongMacdonald.coefW u.val b.val.1 b.val.2 := by
  rfl

end KhanSL2.Macdonald
