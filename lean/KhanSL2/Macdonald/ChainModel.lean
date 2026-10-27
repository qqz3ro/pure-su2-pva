module

public import KhanSL2.Macdonald.SymmetricCoefficientsModule
public import KhanSL2.Factorization.RelativeChains

@[expose] public section
set_option backward.isDefEq.respectTransparency false

/-! The genuine CE chain differential with symmetric current coefficients,
transported to the mixed monomial vector space. Its square-zero identity is
inherited from the actual free CE resolution, not imposed as a field. -/

noncomputable section
open scoped TensorProduct BigOperators
namespace KhanSL2.Macdonald

/-- Swap exterior/coefficient factors and forget the coefficient wrapper. -/
def chainModel : Factorization.RawChains SymmetricCoefficients ≃ₗ[ℂ] W :=
  (TensorProduct.congr (LinearEquiv.refl ℂ Exterior)
    symmetricCoefficientsEquiv.toLinearEquiv).trans (TensorProduct.comm ℂ Exterior Poly)

@[simp] theorem chainModel_tmul (ω : Exterior) (p : SymmetricCoefficients) :
    chainModel (ω ⊗ₜ[ℂ] p) = symmetricCoefficientsEquiv p ⊗ₜ[ℂ] ω := rfl

@[simp] theorem chainModel_symm_tmul (p : Poly) (ω : Exterior) :
    chainModel.symm (p ⊗ₜ[ℂ] ω) = ω ⊗ₜ[ℂ] symmetricCoefficientsEquiv.symm p := rfl

/-- The actual symmetric-coefficient CE boundary in the mixed coordinates. -/
def chainBoundary : Module.End ℂ W :=
  chainModel.toLinearMap.comp
    ((Factorization.rawDifferential SymmetricCoefficients).comp chainModel.symm.toLinearMap)

theorem chainBoundary_chainModel (u : Factorization.RawChains SymmetricCoefficients) :
    chainBoundary (chainModel u) =
      chainModel (Factorization.rawDifferential SymmetricCoefficients u) := by
  simp [chainBoundary]

theorem chainBoundary_square_zero (u : W) : chainBoundary (chainBoundary u) = 0 := by
  obtain ⟨v,rfl⟩ := chainModel.surjective u
  rw [chainBoundary_chainModel, chainBoundary_chainModel]
  have h := LinearMap.congr_fun
    (Factorization.rawDifferential_comp_self SymmetricCoefficients) v
  change Factorization.rawDifferential SymmetricCoefficients
    (Factorization.rawDifferential SymmetricCoefficients v) = 0 at h
  rw [h, map_zero]

theorem chainBoundary_comp_self : chainBoundary.comp chainBoundary = 0 :=
  LinearMap.ext chainBoundary_square_zero

/-- Finite formula for the actual coefficient and bracket terms. -/
theorem chainBoundary_tmul (S : Finset Mode) (p : Poly) (ω : Exterior)
    (hω : FiniteExterior.supportModes ω ⊆ S) :
    chainBoundary (p ⊗ₜ[ℂ] ω) = p ⊗ₜ[ℂ] BGG.PositiveCE.boundary ω -
      ∑ k ∈ S, currentAction (BGG.FreeCE.lieGenerator k : BGG.Current) p ⊗ₜ[ℂ]
        BGG.PositiveCE.contract k ω := by
  change chainModel (Factorization.rawDifferential SymmetricCoefficients
    (ω ⊗ₜ[ℂ] symmetricCoefficientsEquiv.symm p)) = _
  rw [Factorization.rawDifferential_tmul SymmetricCoefficients S ω hω, map_sub, map_sum]
  simp only [chainModel_tmul, symmetricCoefficientsEquiv.apply_symm_apply,
    symmetricCoefficients_lie]

@[simp] theorem chainBoundary_tmul_one (p : Poly) :
    chainBoundary (p ⊗ₜ[ℂ] (1 : Exterior)) = 0 := by
  change chainModel (Factorization.rawDifferential SymmetricCoefficients
    ((1 : Exterior) ⊗ₜ[ℂ] symmetricCoefficientsEquiv.symm p)) = 0
  rw [Factorization.rawDifferential_one_tmul, map_zero]

end KhanSL2.Macdonald
