module

public import KhanSL2.Factorization.WeightedRootModelBlockEquivariance

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The actual signed invariant summand inclusion into the factor-root algebra. -/
def factorSignedInclusion (q r : ℕ) (f : A[X]) :
    FactorSignedModule q r f →ₗ[A] FactorRoots q r f :=
  (FiberTransport.fixedVectors (factorSignedAction q r f)).subtype.comp
    (factorSignedEquiv q r f).toLinearMap

theorem factorSignedInclusion_injective (q r : ℕ) (f : A[X]) :
    Function.Injective (factorSignedInclusion q r f) :=
  Subtype.val_injective.comp (factorSignedEquiv q r f).injective

variable {q₁ q₂ r₁ r₂ : ℕ}
variable [Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A]
variable (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)

/-- The signed factor equivalence has exactly the literal root-restriction
component after inclusion in the actual two factor algebras. -/
theorem blockSignedFactorEquiv_inclusion
    (z : (signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c).stabilizerFixed
      (firstWeightedAssignment q₁ q₂ r₁ r₂)) :
    TensorProduct.map (factorSignedInclusion q₁ r₁ c.f₁) (factorSignedInclusion q₂ r₂ c.f₂)
      (blockSignedFactorEquiv c z) = blockAssignmentTensorEquiv c z.val := by
  obtain ⟨w,rfl⟩ := (blockSignedFactorEquiv c).symm.surjective z
  rw [(blockSignedFactorEquiv c).apply_symm_apply]
  let E := FiberTransport.tensorFixedEquiv (factorSignedAction q₁ r₁ c.f₁)
    (factorSignedAction q₂ r₂ c.f₂) (factorNormalization q₁ r₁) (factorNormalization q₂ r₂)
    (factorNormalization_mul_card q₁ r₁) (factorNormalization_mul_card q₂ r₂)
  let F := TensorProduct.congr (factorSignedEquiv q₁ r₁ c.f₁) (factorSignedEquiv q₂ r₂ c.f₂)
  change TensorProduct.map (factorSignedInclusion q₁ r₁ c.f₁) (factorSignedInclusion q₂ r₂ c.f₂) w =
    blockAssignmentTensorEquiv c ((blockAssignmentTensorEquiv c).symm ((E (F w)).val))
  rw [AlgEquiv.apply_symm_apply]
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,Submodule.coe_add,hx,hy]
  | tmul x y => rfl

end KhanSL2.Factorization.WeightedRootModel

