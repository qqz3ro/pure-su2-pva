module

public import KhanSL2.CanonicalMap
public import KhanSL2.CohomologyGrading
public import KhanSL2.Injectivity.SectorLinearSeparation
public import KhanSL2.Injectivity.TaylorSeparation

@[expose] public section

/-! Assembling sectorwise separation for the already defined canonical map. -/

noncomputable section

namespace KhanSL2.Injectivity

open Source

/-- The component of the actual canonical map is the image of the matching source sector. -/
theorem phi_sector_component
    (a : DirectSum SectorIndex fun t => indexedSector t) (t : SectorIndex) :
    cohomologyDecomposition.components (phi (DirectSum.coeLinearMap indexedSector a))
      (sectorDegree t.1 t.2.1 t.2.2) = phi (a t) := by
  apply linear_sector_component phi cohomologyDecomposition.components
  intro u b hb
  exact cohomologyDecomposition.homogeneous _ _
    (phi_degree (sector_le_piece u.1 u.2.1 u.2.2 hb))

/-- Finite sector decomposition upgrades sectorwise kernel separation to injectivity. -/
theorem phi_injective_of_sector_kernel
    (hsector : ∀ (r s N : ℕ) (a : Source), a ∈ sector r s N → phi a = 0 → a = 0) :
    Function.Injective phi := by
  apply linear_injective_of_sector_kernel phi cohomologyDecomposition.components ?_ hsector
  intro u a ha
  exact cohomologyDecomposition.homogeneous _ _
    (phi_degree (sector_le_piece u.1 u.2.1 u.2.2 ha))

/-- Realization of all source Taylor polynomials by target functionals implies
injectivity of the already defined map. `KhanSL2.phi_injective` supplies this
realization using explicit closed chains. -/
theorem phi_injective_of_taylor_realization
    (realize : ∀ (r s N : ℕ) (ell : Source →ₗ[ℂ] ℂ),
      ∃ targetEll : Cohomology →ₗ[ℂ] ℂ,
        SourceDual.taylorPolynomial r s N (targetEll.comp phi) =
          SourceDual.taylorPolynomial r s N ell) : Function.Injective phi := by
  apply phi_injective_of_sector_kernel
  intro r s N a ha hphi
  exact SourceDual.sector_kernel_eq_zero_of_taylor_realization r s N phi
    (realize r s N) ha hphi

end KhanSL2.Injectivity
