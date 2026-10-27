module

public import KhanSL2.Macdonald.WeightedFirstOrbitFactor
public import KhanSL2.Macdonald.RootHomologyFactorSpecialization

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel
open scoped WeightedFactorScalars

private theorem evaluation_transport {R G I : Type*} [CommRing R] [Group G] [MulAction G I]
    {M : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (T : FiberTransport (R:=R) (G:=G) M) {i j : I} (h : i=j) (z : T.invariantSections) :
    (show T.stabilizerFixed i ≃ₗ[R] T.stabilizerFixed j from by rw [h])
      (T.evaluation i z) = T.evaluation j z := by
  subst i
  rfl

variable {q₁ q₂ r₁ r₂ : ℕ} {A : Type} [CommRing A]
variable [Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A] [Algebra ℂ A]
variable (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)

omit [Algebra ℂ A] in
/-- Canonical orbit reindexing evaluates the same actual invariant section. -/
theorem firstOrbitStabilizerEquiv_orbit
    (z : A ⊗[Depth.RB ((q₁+q₂)+2*(r₁+r₂))] signedInvariantModule (q₁+q₂) (r₁+r₂)) :
    firstOrbitStabilizerEquiv c
      (signedInvariantOrbitEquiv (q₁+q₂) (r₁+r₂) A c z (firstWeightedOrbitIndex q₁ q₂ r₁ r₂)) =
      (signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c).evaluation
        (firstWeightedAssignment q₁ q₂ r₁ r₂)
        (signedInvariantSectionsEquiv (q₁+q₂) (r₁+r₂) A c z) := by
  exact evaluation_transport (signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c)
    (orbitRepresentative_firstWeightedOrbitIndex q₁ q₂ r₁ r₂)
    (signedInvariantSectionsEquiv (q₁+q₂) (r₁+r₂) A c z)

/-- The first component of the original signed factorization is literal quotient restriction. -/
theorem signedInvariantFactorizationEquiv_first_inclusion
    (a : A) (p : signedInvariantModule (q₁+q₂) (r₁+r₂)) :
    TensorProduct.map (factorSignedInclusion q₁ r₁ c.f₁) (factorSignedInclusion q₂ r₂ c.f₂)
      (firstOrbitFactorEquiv c
        (signedInvariantFactorizationEquiv c (by omega)
          (a ⊗ₜ[Depth.RB ((q₁+q₂)+2*(r₁+r₂))] p)
          (firstWeightedOrbitIndex q₁ q₂ r₁ r₂))) =
      blockRestriction c (a ⊗ₜ[Depth.RB ((q₁+q₂)+2*(r₁+r₂))] p.val) := by
  let z := signedInvariantOrbitEquiv (q₁+q₂) (r₁+r₂) A c
    (a ⊗ₜ[Depth.RB ((q₁+q₂)+2*(r₁+r₂))] p) (firstWeightedOrbitIndex q₁ q₂ r₁ r₂)
  have hz := orbitSignedFactorEquiv_first c (firstOrbitStabilizerEquiv c z)
  rw [LinearEquiv.symm_apply_apply] at hz
  change TensorProduct.map _ _ (firstOrbitFactorEquiv c (orbitSignedFactorEquiv c _ _ z)) = _
  rw [hz]
  dsimp only [z]
  rw [firstOrbitStabilizerEquiv_orbit,blockSignedFactorEquiv_inclusion]
  rfl

variable [IsScalarTower ℂ (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A]

/-- The normalized root block and the original first orbit factor map agree before any scalar normalization. -/
theorem rootHomologyNormalizedBlock_factorization
    (x : RootHomologyModel (q₁+q₂) (r₁+r₂)) :
    weightedRootHomologyTensorUnit q₁ q₂ r₁ r₂ c.f₁ c.f₂
      (rootHomologyNormalizedBlock q₁ q₂ r₁ r₂ x) =
      firstOrbitFactorEquiv c
        (signedInvariantFactorizationEquiv c (by omega)
          (1 ⊗ₜ[Depth.RB ((q₁+q₂)+2*(r₁+r₂))] (rootHomologyModelEquiv (q₁+q₂) (r₁+r₂) x))
          (firstWeightedOrbitIndex q₁ q₂ r₁ r₂)) := by
  apply weightedFactorSignedTensorInclusion_injective
  rw [rootHomologyNormalizedBlock_chart,signedInvariantFactorizationEquiv_first_inclusion]
  rfl

end KhanSL2.Macdonald
