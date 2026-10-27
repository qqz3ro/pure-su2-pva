module

public import KhanSL2.Macdonald.NormalizedSignedRootFactorization
public import KhanSL2.Factorization.WeightedRootModelBlockFormulas

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open scoped TensorProduct
namespace KhanSL2.Macdonald
open Factorization WeightedRootModel

private theorem linearEquiv_transport_cancel {R ι : Type*} [CommRing R]
    (S : ι → Type*) [∀ i, AddCommGroup (S i)] [∀ i, Module R (S i)]
    (F : ℕ → ℕ → Type*) [∀ a b, AddCommGroup (F a b)] [∀ a b, Module R (F a b)]
    {i j : ι} {a b c d : ℕ} (hij : i=j) (hab : a=b) (hcd : c=d)
    (e : S j ≃ₗ[R] F b d) (x : S j) :
    (show F a c ≃ₗ[R] F b d from by rw [hab,hcd])
      ((show S i ≃ₗ[R] F a c from by rw [hij,hab,hcd]; exact e)
        ((show S i ≃ₗ[R] S j from by rw [hij]).symm x)) = e x := by
  subst i
  subst a
  subst c
  rfl

variable {q₁ q₂ r₁ r₂ : ℕ} {A : Type} [CommRing A]
variable [Algebra (Depth.RB ((q₁+q₂)+2*(r₁+r₂))) A] [Algebra ℂ A]
variable (c : Collision.ChartData ((q₁+q₂)+2*(r₁+r₂)) (q₁+2*r₁) (q₂+2*r₂) A)

/-- Only the canonical subtraction identities are transported in the first orbit's target. -/
def firstOrbitFactorEquiv :
    OrbitFactor c (firstWeightedOrbitIndex q₁ q₂ r₁ r₂) ≃ₗ[A]
      FactorSignedModule q₁ r₁ c.f₁ ⊗[A] FactorSignedModule q₂ r₂ c.f₂ := by
  change (FactorSignedModule q₁ r₁ c.f₁ ⊗[A]
    FactorSignedModule ((q₁+q₂)-q₁) ((r₁+r₂)-r₁) c.f₂) ≃ₗ[A] _
  rw [Nat.add_sub_cancel_left,Nat.add_sub_cancel_left]

/-- The canonical orbit representative is the original first weighted assignment. -/
def firstOrbitStabilizerEquiv :
    (signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c).stabilizerFixed
      (orbitRepresentative (firstWeightedOrbitIndex q₁ q₂ r₁ r₂)) ≃ₗ[A]
      (signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c).stabilizerFixed
        (firstWeightedAssignment q₁ q₂ r₁ r₂) := by
  rw [orbitRepresentative_firstWeightedOrbitIndex]

/-- The first orbit comparison is exactly the already proved literal signed block comparison. -/
theorem orbitSignedFactorEquiv_first
    (z : (signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c).stabilizerFixed
      (firstWeightedAssignment q₁ q₂ r₁ r₂)) :
    firstOrbitFactorEquiv c
      (orbitSignedFactorEquiv c (by omega) (firstWeightedOrbitIndex q₁ q₂ r₁ r₂)
        ((firstOrbitStabilizerEquiv c).symm z)) = blockSignedFactorEquiv c z := by
  rw [orbitSignedFactorEquiv_eq_ofAdd c _ _ q₂ r₂ rfl rfl]
  simpa only [firstOrbitFactorEquiv,firstOrbitStabilizerEquiv,orbitSignedFactorEquivOfAdd,
    firstWeightedOrbitIndex,OrbitFactor,OrbitIndex,LinearEquiv.refl_symm,LinearEquiv.refl_apply,
    id_eq,eq_mpr_eq_cast,cast_cast,cast_eq] using
    linearEquiv_transport_cancel
      (fun σ => (signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c).stabilizerFixed σ)
      (fun a b => FactorSignedModule q₁ r₁ c.f₁ ⊗[A] FactorSignedModule a b c.f₂)
      (orbitRepresentative_firstWeightedOrbitIndex q₁ q₂ r₁ r₂)
      (Nat.add_sub_cancel_left q₁ q₂) (Nat.add_sub_cancel_left r₁ r₂)
      (blockSignedFactorEquiv c) z

end KhanSL2.Macdonald

