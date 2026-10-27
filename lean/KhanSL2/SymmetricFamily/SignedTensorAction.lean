module

public import KhanSL2.SymmetricFamily.SignedRepresentation

@[expose] public section
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct
namespace KhanSL2.SymmetricFamily
open Factorization.FiberTransport

/-- Independent scalar characters multiply under the actual tensor group action. -/
theorem tensorAction_scalarTwist {R G H M N : Type*} [CommRing R] [Group G] [Group H]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (χ : G →* Rˣ) (ψ : H →* Rˣ) (ρ : G →* Module.End R M) (τ : H →* Module.End R N)
    (g : G × H) (x : M ⊗[R] N) :
    tensorAction (scalarTwistRepresentation χ ρ) (scalarTwistRepresentation ψ τ) g x =
      ((χ g.1 : R) * (ψ g.2 : R)) • tensorAction ρ τ g x := by
  change TensorProduct.map ((χ g.1 : R) • ρ g.1) ((ψ g.2 : R) • τ g.2) x = _
  rw [TensorProduct.map_smul_left,TensorProduct.map_smul_right,smul_smul]
  rfl

end KhanSL2.SymmetricFamily
