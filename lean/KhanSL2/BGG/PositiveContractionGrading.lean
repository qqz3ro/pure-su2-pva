module

public import KhanSL2.BGG.PositiveContraction
public import KhanSL2.BGG.PositiveBoundaryEquivariance

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! The actual Hodge contraction preserves energy and is equivariant for the
constant sl₂ action. Its homotopy raises exterior degree by one. -/

noncomputable section
namespace KhanSL2.BGG.PositiveCE

private theorem laplacian_bidegreeProjection (q : ℕ × ℕ) :
    Commute laplacian (BasisGrading.projection bidegree q) := by
  apply LinearMap.ext
  intro u
  exact (BasisGrading.projection_linearMap bidegree laplacian id Function.injective_id
    (fun k v hv => (mem_bidegree_piece k _).mpr
      (laplacian_mem_piece ((mem_bidegree_piece k v).mp hv))) q u).symm

/-- The canonical Green operator commutes with every homogeneous projection. -/
theorem green_bidegreeProjection (q : ℕ × ℕ) (u : Cochain) :
    green (BasisGrading.projection bidegree q u) =
      BasisGrading.projection bidegree q (green u) :=
  LinearMap.congr_fun (Spectral.green_commute laplacian laplacian_isCompl_ker_range
    (BasisGrading.projection bidegree q) (laplacian_bidegreeProjection q)).eq u

/-- Green preserves both exterior degree and physical energy. -/
theorem green_mem_piece {p N : ℕ} {u : Cochain} (hu : u ∈ piece p N) :
    green u ∈ piece p N := by
  have hu' := (mem_bidegree_piece (p,N) u).mpr hu
  apply (mem_bidegree_piece (p,N) _).mp
  have heq : BasisGrading.projection bidegree (p,N) (green u) = green u := by
    rw [← green_bidegreeProjection, BasisGrading.projection_of_mem bidegree hu']
  rw [← heq]
  exact BasisGrading.projection_mem bidegree (p,N) (green u)

/-- Harmonic projection is identity minus Laplacian followed by Green. -/
theorem harmonicProjection_coe (u : Cochain) :
    (harmonicProjection u : Cochain) = u - laplacian (green u) := by
  have h := LinearMap.congr_fun (Spectral.f_mul_green laplacian laplacian_isCompl_ker_range) u
  change laplacian (green u) = u - (harmonicProjection u : Cochain) at h
  rw [h]
  abel

/-- Harmonic projection preserves both degree and energy. -/
theorem harmonicProjection_mem_piece {p N : ℕ} {u : Cochain} (hu : u ∈ piece p N) :
    (harmonicProjection u : Cochain) ∈ piece p N := by
  rw [harmonicProjection_coe]
  exact (piece p N).sub_mem hu (laplacian_mem_piece (green_mem_piece hu))

/-- The actual Laplacian commutes with every constant sl₂ action. -/
theorem laplacian_positiveAction (x : G) (u : Cochain) :
    laplacian (ColorRoot.positiveAction x u) = ColorRoot.positiveAction x (laplacian u) := by
  simp only [laplacian_apply, boundary_positiveAction, ColorRoot.d_positiveAction, map_add]

/-- The canonical Green operator is sl₂-equivariant. -/
theorem green_positiveAction (x : G) (u : Cochain) :
    green (ColorRoot.positiveAction x u) = ColorRoot.positiveAction x (green u) := by
  have hcomm : Commute laplacian (ColorRoot.positiveAction x) := by
    apply LinearMap.ext
    exact laplacian_positiveAction x
  exact LinearMap.congr_fun (Spectral.green_commute laplacian laplacian_isCompl_ker_range
    (ColorRoot.positiveAction x) hcomm).eq u

/-- The actual harmonic projection is sl₂-equivariant. -/
theorem harmonicProjection_positiveAction (x : G) (u : Cochain) :
    (harmonicProjection (ColorRoot.positiveAction x u) : Cochain) =
      ColorRoot.positiveAction x (harmonicProjection u : Cochain) := by
  rw [harmonicProjection_coe, harmonicProjection_coe, green_positiveAction,
    laplacian_positiveAction, map_sub]

/-- The actual harmonic kernel is a Lie submodule, because the Laplacian is equivariant. -/
def harmonicLieSubmodule : LieSubmodule ℂ G Cochain :=
  { LinearMap.ker laplacian with
    lie_mem := fun {x u} hu => by
      change laplacian (ColorRoot.positiveAction x u) = 0
      rw [laplacian_positiveAction, show laplacian u = 0 from hu, map_zero] }

instance : LieRingModule G Harmonic :=
  inferInstanceAs (LieRingModule G harmonicLieSubmodule)

instance : LieModule ℂ G Harmonic :=
  inferInstanceAs (LieModule ℂ G harmonicLieSubmodule)

@[simp] theorem harmonic_lie_coe (x : G) (u : Harmonic) :
    (⁅x,u⁆ : Cochain) = ColorRoot.positiveAction x (u : Cochain) := rfl

/-- Inclusion of actual harmonics, bundled as a morphism of sl₂ modules. -/
def harmonicInclusionLie : Harmonic →ₗ⁅ℂ,G⁆ Cochain :=
  { Harmonic.subtype with map_lie' := rfl }

/-- Projection onto actual harmonics, bundled as a morphism of sl₂ modules. -/
def harmonicProjectionLie : Cochain →ₗ⁅ℂ,G⁆ Harmonic :=
  { harmonicProjection with
    map_lie' := fun {x u} => Subtype.ext (harmonicProjection_positiveAction x u) }

/-- The actual Green operator as a morphism of sl₂ modules. -/
def greenLie : Cochain →ₗ⁅ℂ,G⁆ Cochain :=
  { green with map_lie' := fun {x u} => green_positiveAction x u }

/-- The actual chain-contraction homotopy as a morphism of sl₂ modules. -/
def homotopyLie : Cochain →ₗ⁅ℂ,G⁆ Cochain := dLie.comp greenLie

@[simp] theorem homotopyLie_apply (u : Cochain) : homotopyLie u = d (green u) := rfl

@[simp] theorem chainContraction_homotopy_apply (u : Cochain) :
    chainContraction.homotopy u = d (green u) := rfl

/-- The actual homotopy raises chain degree by one and preserves physical energy. -/
theorem homotopy_mem_piece {p N : ℕ} {u : Cochain} (hu : u ∈ piece p N) :
    chainContraction.homotopy u ∈ piece (p+1) N :=
  d_mem_piece (green_mem_piece hu)

end KhanSL2.BGG.PositiveCE
