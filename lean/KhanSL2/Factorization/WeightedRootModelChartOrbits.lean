module

public import KhanSL2.Factorization.WeightedRootModelChartAction
public import KhanSL2.Factorization.WeightedRootModelOrbits

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel

variable (q r : ℕ) (A : Type) [CommRing A] [Algebra (Depth.RB (q+2*r)) A]

/-- Canonical decomposition of the actual signed weighted-root family into its
admissible block components. Every component is literal quotient restriction. -/
def signedInvariantOrbitEquiv {b₁ b₂ : ℕ} (c : Collision.ChartData (q+2*r) b₁ b₂ A) :
    (A ⊗[Depth.RB (q+2*r)] signedInvariantModule q r) ≃ₗ[A]
      ∀ d : OrbitIndex q r b₁,
        (signedAssignmentTransport q r A c).stabilizerFixed (orbitRepresentative d) :=
  (signedInvariantSectionsEquiv q r A c).trans
    (weightedOrbitEvaluationEquiv (signedAssignmentTransport q r A c))

@[simp] theorem signedInvariantOrbitEquiv_tmul {b₁ b₂ : ℕ}
    (c : Collision.ChartData (q+2*r) b₁ b₂ A) (a : A) (p : signedInvariantModule q r)
    (d : OrbitIndex q r b₁) :
    (signedInvariantOrbitEquiv q r A c (a ⊗ₜ[Depth.RB (q+2*r)] p) d).val =
      Ideal.Quotient.mk (assignmentIdeal q r A c (orbitRepresentative d))
        (a ⊗ₜ[Depth.RB (q+2*r)] p.val) := rfl

end KhanSL2.Factorization.WeightedRootModel
