module

public import KhanSL2.Factorization.OrbitStabilizerDecomposition

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace KhanSL2.Factorization.FiberTransport
variable {R G V W : Type*} [CommRing R] [Group G]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- Restrict a specified equivariant linear equivalence to the actual fixed modules. -/
def fixedVectorsCongr (ρ : G → Module.End R V) (τ : G → Module.End R W)
    (e : V ≃ₗ[R] W) (he : ∀ g x, e (ρ g x) = τ g (e x)) :
    fixedVectors ρ ≃ₗ[R] fixedVectors τ where
  toFun x := ⟨e x.val, fun g => (he g x.val).symm.trans (congrArg e (x.property g))⟩
  invFun y := ⟨e.symm y.val, by
    intro g
    apply e.injective
    rw [he,LinearEquiv.apply_symm_apply,y.property g]⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (e.map_add x.val y.val)
  map_smul' c x := Subtype.ext (e.map_smul c x.val)

omit [Group G] in
@[simp] theorem fixedVectorsCongr_apply (ρ : G → Module.End R V) (τ : G → Module.End R W)
    (e : V ≃ₗ[R] W) (he : ∀ g x, e (ρ g x) = τ g (e x)) (x : fixedVectors ρ) :
    (fixedVectorsCongr ρ τ e he x).val = e x.val := rfl

end KhanSL2.Factorization.FiberTransport

