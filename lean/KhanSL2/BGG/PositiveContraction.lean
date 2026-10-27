module

public import KhanSL2.BGG.PositiveHarmonics
public import KhanSL2.BGG.GradedSpectralSplitting
public import KhanSL2.BGG.GreenOperator
public import KhanSL2.BGG.HodgeContraction

@[expose] public section
noncomputable section
namespace KhanSL2.BGG.PositiveCE

/-- The actual Laplacian has complementary kernel and range on finite cochains. -/
theorem laplacian_isCompl_ker_range :
    IsCompl (LinearMap.ker laplacian) (LinearMap.range laplacian) := by
  rw [laplacian_eq_energyCasimir]
  exact energyCasimir_isCompl_ker_range

/-- The actual harmonic space, not an assumed model for homology. -/
abbrev Harmonic := LinearMap.ker laplacian

/-- The canonical algebraic inverse of the Laplacian off its harmonic kernel. -/
def green : Module.End ℂ Cochain := Spectral.green laplacian laplacian_isCompl_ker_range

def harmonicProjection : Cochain →ₗ[ℂ] Harmonic :=
  (LinearMap.ker laplacian).projectionOnto (LinearMap.range laplacian)
    laplacian_isCompl_ker_range

theorem laplacian_commute_d : Commute laplacian d := by
  apply LinearMap.ext
  exact laplacian_d

theorem laplacian_commute_boundary : Commute laplacian boundary := by
  apply LinearMap.ext
  exact laplacian_boundary

private theorem projection_d (u : Cochain) : harmonicProjection (d u) = 0 :=
  (LinearMap.ker laplacian).projectionOnto_apply_of_mem_right laplacian_isCompl_ker_range
    (Spectral.map_mem_range_of_kills_ker laplacian laplacian_isCompl_ker_range d
      laplacian_commute_d (fun _ h => d_eq_zero_of_laplacian_eq_zero h) u)

private theorem projection_boundary (u : Cochain) : harmonicProjection (boundary u) = 0 :=
  (LinearMap.ker laplacian).projectionOnto_apply_of_mem_right laplacian_isCompl_ker_range
    (Spectral.map_mem_range_of_kills_ker laplacian laplacian_isCompl_ker_range boundary
      laplacian_commute_boundary (fun _ h => boundary_eq_zero_of_laplacian_eq_zero h) u)

/-- A proved special contraction of the actual positive-current homology complex
onto its actual harmonic space. Its homotopy is the coboundary times the Green operator. -/
def chainContraction : TauCeti.LinearSpecialContraction boundary (0 : Module.End ℂ Harmonic) :=
  contractionOfLaplacian boundary d green Harmonic.subtype harmonicProjection
    (by
      apply LinearMap.ext
      intro u
      exact (LinearMap.ker laplacian).projectionOnto_apply_left laplacian_isCompl_ker_range u)
    (by
      apply LinearMap.ext
      intro u
      exact boundary_eq_zero_of_laplacian_eq_zero u.property)
    (by
      apply LinearMap.ext
      exact projection_boundary)
    (by
      apply LinearMap.ext
      exact d_square_zero)
    (Spectral.green_commute laplacian laplacian_isCompl_ker_range boundary laplacian_commute_boundary)
    (Spectral.green_commute laplacian laplacian_isCompl_ker_range d laplacian_commute_d)
    (by
      apply LinearMap.ext
      intro u
      exact Spectral.green_eq_zero_of_mem_ker laplacian laplacian_isCompl_ker_range u.property)
    (by
      apply LinearMap.ext
      exact projection_d)
    (by
      have h := Spectral.f_mul_green laplacian laplacian_isCompl_ker_range
      have hL : boundary * d + d * boundary = laplacian := by
        simp only [laplacian, Module.End.mul_eq_comp, add_comm]
      rw [hL]
      exact h)

/-- The contraction identity explicitly expresses any cycle as a harmonic
representative plus a boundary. -/
theorem boundary_homotopy_add_homotopy_boundary (u : Cochain) :
    boundary (d (green u)) + d (green (boundary u)) =
      u - (harmonicProjection u : Cochain) :=
  LinearMap.congr_fun chainContraction.dM_comp_homotopy_add_homotopy_comp_dM u

end KhanSL2.BGG.PositiveCE