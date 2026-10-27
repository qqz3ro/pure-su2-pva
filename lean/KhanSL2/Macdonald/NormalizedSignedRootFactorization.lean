module

public import KhanSL2.Factorization.WeightedRootModelSplitting
public import KhanSL2.Macdonald.RootFactorizationNormalization

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped TensorProduct
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel

variable {q r s₁ s₂ : ℕ} {A : Type} [CommRing A]
variable [Algebra (Depth.RB (q+2*r)) A] [Algebra ℂ A]
variable (c : Collision.ChartData (q+2*r) s₁ s₂ A)

/-- The exact nonzero root-block coefficient remains a unit over every chart algebra. -/
def rootOrbitNormalizationUnit (d : OrbitIndex q r s₁) : Aˣ :=
  Units.map (algebraMap ℂ A).toMonoidHom
    (Units.mk0 (rootFactorizationNormalization q r d.val.1 d.val.2)
      (rootFactorizationNormalization_ne_zero d.property.1 d.property.2.1))

omit [Algebra (Depth.RB (q+2*r)) A] in
@[simp] theorem rootOrbitNormalizationUnit_val (d : OrbitIndex q r s₁) :
    (rootOrbitNormalizationUnit (A := A) d : A) =
      algebraMap ℂ A (rootFactorizationNormalization q r d.val.1 d.val.2) := rfl

/-- Componentwise multiplication by the actual normalized coproduct coefficients. -/
def rootOrbitNormalizationEquiv :
    (∀ d : OrbitIndex q r s₁, OrbitFactor c d) ≃ₗ[A]
      (∀ d : OrbitIndex q r s₁, OrbitFactor c d) :=
  LinearEquiv.piCongrRight (fun d => LinearEquiv.smulOfUnit (rootOrbitNormalizationUnit (A := A) d))

@[simp] theorem rootOrbitNormalizationEquiv_apply
    (z : ∀ d : OrbitIndex q r s₁, OrbitFactor c d) (d : OrbitIndex q r s₁) :
    rootOrbitNormalizationEquiv c z d =
      algebraMap ℂ A (rootFactorizationNormalization q r d.val.1 d.val.2) • z d := rfl

/-- The normalized literal chart restriction, including its exact odd/even binomial coefficient in every block. -/
def normalizedSignedRootFactorizationMap (htotal : s₁+s₂=q+2*r) :
    (A ⊗[Depth.RB (q+2*r)] signedInvariantModule q r) →ₗ[A]
      ∀ d : OrbitIndex q r s₁, OrbitFactor c d :=
  (rootOrbitNormalizationEquiv c).toLinearMap.comp
    (signedInvariantFactorizationEquiv c htotal).toLinearMap

@[simp] theorem normalizedSignedRootFactorizationMap_apply (htotal : s₁+s₂=q+2*r)
    (z : A ⊗[Depth.RB (q+2*r)] signedInvariantModule q r) (d : OrbitIndex q r s₁) :
    normalizedSignedRootFactorizationMap c htotal z d =
      algebraMap ℂ A (rootFactorizationNormalization q r d.val.1 d.val.2) •
        signedInvariantFactorizationEquiv c htotal z d := rfl

/-- Multiplying the proved literal quotient restrictions by the exact nonzero coefficients preserves bijectivity. -/
theorem normalizedSignedRootFactorizationMap_bijective (htotal : s₁+s₂=q+2*r) :
    Function.Bijective (normalizedSignedRootFactorizationMap c htotal) :=
  (rootOrbitNormalizationEquiv c).bijective.comp
    (signedInvariantFactorizationEquiv c htotal).bijective

/-- The normalization uses the same actual chart map and works over nonreduced or zero chart algebras. -/
def normalizedSignedRootFactorizationEquiv (htotal : s₁+s₂=q+2*r) :
    (A ⊗[Depth.RB (q+2*r)] signedInvariantModule q r) ≃ₗ[A]
      ∀ d : OrbitIndex q r s₁, OrbitFactor c d :=
  LinearEquiv.ofBijective (normalizedSignedRootFactorizationMap c htotal)
    (normalizedSignedRootFactorizationMap_bijective c htotal)

end KhanSL2.Macdonald
