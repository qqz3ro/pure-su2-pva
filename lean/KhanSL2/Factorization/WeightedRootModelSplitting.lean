module

public import KhanSL2.Factorization.WeightedRootModelBlockEquivariance
public import KhanSL2.Factorization.WeightedRootModelChartOrbits

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace KhanSL2.Factorization.WeightedRootModel

variable {q r b₁ b₂ : ℕ} {A : Type} [CommRing A]
variable [Algebra (Depth.RB (q+2*r)) A] [Algebra ℂ A]
variable (c : Collision.ChartData (q+2*r) b₁ b₂ A)

/-- The factorized signed module attached to an admissible odd/even allocation. -/
abbrev OrbitFactor (d : OrbitIndex q r b₁) :=
  FactorSignedModule d.val.1 d.val.2 c.f₁ ⊗[A]
    FactorSignedModule (q-d.val.1) (r-d.val.2) c.f₂

/-- The original block comparison with specified complementary root counts.
Its target remains the original orbit factor, independent of the selected complement presentation. -/
def orbitSignedFactorEquivOfAdd (htotal : b₁+b₂=q+2*r) (d : OrbitIndex q r b₁)
    (q₂ r₂ : ℕ) (hqeq : q=d.val.1+q₂) (hreq : r=d.val.2+r₂) :
    (signedAssignmentTransport q r A c).stabilizerFixed (orbitRepresentative d) ≃ₗ[A]
      OrbitFactor c d := by
  rcases d with ⟨⟨q₁,r₁⟩,hq,hr,hb⟩
  dsimp only at hqeq hreq
  subst q
  subst r
  have hb₂ : b₂=q₂+2*r₂ := by omega
  subst b₁
  subst b₂
  change (signedAssignmentTransport (q₁+q₂) (r₁+r₂) A c).stabilizerFixed
      (orbitRepresentative (firstWeightedOrbitIndex q₁ q₂ r₁ r₂)) ≃ₗ[A]
        FactorSignedModule q₁ r₁ c.f₁ ⊗[A]
          FactorSignedModule ((q₁+q₂)-q₁) ((r₁+r₂)-r₁) c.f₂
  rw [orbitRepresentative_firstWeightedOrbitIndex,Nat.add_sub_cancel_left,Nat.add_sub_cancel_left]
  exact blockSignedFactorEquiv c

/-- The canonical orbit component is exactly the two corresponding smaller
weighted signed modules, using the original complementary counts. -/
def orbitSignedFactorEquiv (htotal : b₁+b₂=q+2*r) (d : OrbitIndex q r b₁) :
    (signedAssignmentTransport q r A c).stabilizerFixed (orbitRepresentative d) ≃ₗ[A]
      OrbitFactor c d :=
  orbitSignedFactorEquivOfAdd c htotal d (q-d.val.1) (r-d.val.2)
    (by have h := d.property.1; omega) (by have h := d.property.2.1; omega)

/-- Changing only the presentation of the complementary counts does not change the actual orbit map. -/
theorem orbitSignedFactorEquiv_eq_ofAdd (htotal : b₁+b₂=q+2*r) (d : OrbitIndex q r b₁)
    (q₂ r₂ : ℕ) (hqeq : q=d.val.1+q₂) (hreq : r=d.val.2+r₂) :
    orbitSignedFactorEquiv c htotal d = orbitSignedFactorEquivOfAdd c htotal d q₂ r₂ hqeq hreq := by
  have hq : q-d.val.1=q₂ := by omega
  have hr : r-d.val.2=r₂ := by omega
  simp only [orbitSignedFactorEquiv,hq,hr]

/-- Coprime factorization for the actual signed weighted-root coefficient module,
valid on every chart, including arbitrary nonreduced coefficient rings. -/
def signedInvariantFactorizationEquiv (htotal : b₁+b₂=q+2*r) :
    (A ⊗[Depth.RB (q+2*r)] signedInvariantModule q r) ≃ₗ[A]
      ∀ d : OrbitIndex q r b₁, OrbitFactor c d :=
  (signedInvariantOrbitEquiv q r A c).trans
    (LinearEquiv.piCongrRight (orbitSignedFactorEquiv c htotal))

end KhanSL2.Factorization.WeightedRootModel



